Any_plus = '<$.+>'
Any_one = '<$.>'
def Any_not(t): return '<!%s>' % t
def is_not(t):
    if len(t) > 1:
        if  t[1] == '!':
            return t[2]
    return None

def is_not_match(letter, col_letter):
    l = is_not(letter)
    if l is not None:
        return l != col_letter
    else:
        return False

def letter_match(letter, col_letter):
    if letter == col_letter: return True
        # letter can be any: <$.+> or not: <!x>
    if letter == Any_one: return True
    if is_not_match(letter, col_letter): return True
    return False


def new_start(old_start):
    old_start_ = old_start[1:-1]
    return '<$%s>' % old_start_

def add_start(g_, old_start):
    g = dict(g_)
    new_start_sym = new_start(old_start)
    g[new_start_sym] = [
            add_weight([old_start], 0),
            add_weight([old_start, Any_plus], 0)]
    g[Any_plus] = [
            add_weight([Any_plus, Any_one], 1),
            add_weight([Any_one], 1),
            ]
    return g

def print_g(g):
    for k in g:
        print(k)
        for rule in g[k]:
            print('  ', rule)

def add_weight(rule, weight):
    assert isinstance(rule, list)
    return [tuple(rule), weight]

def add_weights_to_grammar(g):
    return {k:[add_weight(rule, 0) for rule in g[k]] for k in g}

def fix_terminal(g, t):
    nt_t = to_term(t)
    if nt_t not in g:
        g[nt_t] = [
                add_weight([t], 0),
                add_weight([Any_plus, t], 0),
                add_weight([], 1),
                add_weight([Any_not(t)], 1)
        ]

def to_term(t): return '<$ %s>' % t


def fix_weighted_terminals(g):
    terms = set()
    keys = [k for k in g]
    for k in keys:
        for alt,w in g[k]:
            for t in alt:
                if t not in g:
                    fix_terminal(g, t)

class Column:
    def __init__(self, index, letter):
        self.index, self.letter = index, letter
        self.states, self._unique = [], {}

    def __str__(self):
        return "%s chart[%d]\n%s" % (self.letter, self.index, "\n".join(
            str(state) for state in self.states if state.finished()))

    def add(self, state):
        if state in self._unique:
            return self._unique[state]
        self._unique[state] = state
        self.states.append(state)
        state.e_col = self
        return self._unique[state]


class State:
    def __init__(self, name, expr, dot, s_col, e_col=None):
        self.name, self.expr_, self.dot = name, expr, dot
        self.s_col, self.e_col = s_col, e_col
        self.expr, self.weight = self.expr_

    def finished(self):
        return self.dot >= len(self.expr)

    def at_dot(self):
        return self.expr[self.dot] if self.dot < len(self.expr) else None

    def __str__(self):
        def idx(var):
            return var.index if var else -1

        return self.name + ':= ' + ' '.join([
            str(p)
            for p in [*self.expr[:self.dot], '|', *self.expr[self.dot:]]
        ]) + "(%d,%d)" % (idx(self.s_col), idx(self.e_col))

    def copy(self):
        return State(self.name, self.expr_, self.dot, self.s_col, self.e_col)

    def _t(self):
        return (self.name, self.expr, self.dot, self.s_col.index)

    def __hash__(self):
        return hash(self._t())

    def __eq__(self, other):
        return self._t() == other._t()

    def advance(self):
        return State(self.name, self.expr_, self.dot + 1, self.s_col)

class Parser:
    def parse_on(self, text, start_symbol):
        raise NotImplemented()

class EarleyParser(Parser):
    def __init__(self, grammar, log=False, **kwargs):
        g_e = add_weights_to_grammar(grammar)
        # need to update terminals
        fix_weighted_terminals(g_e)
        self.epsilon = nullable(grammar)
        self._grammar = g_e
        self.log = log

def is_nt(k):
    return (k[0], k[-1]) == ('<', '>')

def rem_terminals(g):
    g_cur = {}
    for k in g:
        alts = []
        for alt in g[k]:
            ts = [t for t in alt if not is_nt(t)]
            if not ts:
                alts.append(alt)
        if alts:
            g_cur[k] = alts
    return g_cur

def nullable(g):
    nullable_keys = {k for k in g if [] in g[k]}

    unprocessed  = list(nullable_keys)

    g_cur = rem_terminals(g)
    while unprocessed:
        nxt, *unprocessed = unprocessed
        g_nxt = {}
        for k in g_cur:
            g_alts = []
            for alt in g_cur[k]:
                alt_ = [t for t in alt if t != nxt]
                if not alt_:
                    nullable_keys.add(k)
                    unprocessed.append(k)
                    break
                else:
                    g_alts.append(alt_)
            if g_alts:
                g_nxt[k] = g_alts
        g_cur = g_nxt

    return nullable_keys


class EarleyParser(EarleyParser):
    def chart_parse(self, tokens, start, alt):
        chart = [Column(i, tok) for i, tok in enumerate([None, *tokens])]
        chart[0].add(State(start, alt, 0, chart[0]))
        return self.fill_chart(chart)


class EarleyParser(EarleyParser):
    def predict(self, col, sym, state):
        for alt in self._grammar[sym]:
            col.add(State(sym, alt, 0, col))
        if sym in self.epsilon:
            col.add(state.advance())

class EarleyParser(EarleyParser):
    def scan(self, col, state, letter):
        if letter_match(letter, col.letter):
            col.add(state.advance())

class EarleyParser(EarleyParser):
    def complete(self, col, state):
        parent_states = [st for st in state.s_col.states
                 if st.at_dot() == state.name]
        for st in parent_states:
            s = st.advance()
            s.weight += state.weight
            col.add(s)

class EarleyParser(EarleyParser):
    def fill_chart(self, chart):
        for i, col in enumerate(chart):
            for state in col.states:
                if state.finished():
                    self.complete(col, state)
                else:
                    sym = state.at_dot()
                    if sym in self._grammar:
                        self.predict(col, sym, state)
                    else:
                        if i + 1 >= len(chart):
                            continue
                        self.scan(chart[i + 1], state, sym)
            if self.log: print(col, '\n')
        return chart

class EarleyParser(EarleyParser):
    def parse_prefix(self, text, start_symbol, alt):
        self.table = self.chart_parse(text, start_symbol, alt)
        for col in reversed(self.table):
            states = [st for st in col.states
                if st.name == start_symbol and st.expr == alt[0] and st.s_col.index == 0
            ]
            if states:
                return col.index, states
        return -1, []

class EarleyParser(EarleyParser):
    def parse_on(self, text, start_symbol_):
        self._grammar = add_start(self._grammar, start_symbol_)
        start_symbol = new_start(start_symbol_)

        for alt in self._grammar[start_symbol]:
            cursor, states = self.parse_prefix(text, start_symbol, alt)
            start = next((s for s in states if s.finished()), None)

            if cursor < len(text) or not start:
                #raise SyntaxError("at " + repr(text[cursor:]))
                continue
            yield alt
            #forest = self.parse_forest(self.table, start)
            #for tree in self.extract_trees(forest):
            #    yield tree


grammar = {
    '<start>': [['<expr>']],
    '<expr>': [
        ['<term>', '+', '<expr>'],
        ['<term>', '-', '<expr>'],
        ['<term>']],
    '<term>': [
        ['<fact>', '*', '<term>'],
        ['<fact>', '/', '<term>'],
        ['<fact>']],
    '<fact>': [
        ['<digits>'],
        ['(','<expr>',')']],
    '<digits>': [
        ['<digit>','<digits>'],
        ['<digit>']],
    '<digit>': [["%s" % str(i)] for i in range(10)],
}
START = '<start>'


# Modifications:
# Each rule gets a weight
# The start gets changed to:
# <$start>  := [0] <start>
#            | [0] <start> <$.+>
# <$.+>     := [1] <$.+> <$.>
#            | [1] <$.>
# Each terminal gets converted to a nonterminal

#ep = EarleyParser(grammar, log=False)
#cursor, columns = ep.parse_prefix('0', START, add_weight(grammar[START][0], 0))
#print(cursor)
#for c in columns:
#    print(c)


myg = EarleyParser(grammar)
val = myg.parse_on('100+1+1+x+1', START)
for v in val:
    print(v)

