import re
import sys

from parsita import *

from parsita.util import constant


def foldr(f, lst, var):
    for i in lst[::-1]:
        var = f(i, var)
    return var


def make_list(lst, var):
    lst = lst[:lst.rindex('nil')] + var + lst[3 + lst.rindex('nil'):]
    return lst


class PrologParser(TextParsers, whitespace=r'[ \t\n]*'):
    ID = reg(r'[a-z_][a-zA-Z_0-9]*')
    VAR = reg(r'[A-Z_][a-zA-Z_0-9]*')
    TYPEID = reg(r'[a-zA-Z_][a-zA-Z_0-9]*')
    DEF = lit(':-')
    TAIL = lit('.')
    AND = lit(',')
    OR = lit(';')
    LBR = lit('(')
    RBR = lit(')')
    ARR = lit('->')
    TYPE = lit('type')
    MOD = lit('module')
    LBRK = lit('[')
    RBRK = lit(']')
    LOGOR = lit('|')

    trie_definition_long = lambda x: 'DEF(' + x[0] + ',' + x[2] + ')'
    trie_definition_short = lambda x: x[0]
    trie_identifier = lambda x: ' ' + ''.join(x)
    trie_nothing = lambda x: ' ' + ''.join(x)
    trie_var = lambda x: ' ' + ''.join(x)
    trie_conjunction = lambda x: 'AND(' + x[0] + ',' + x[2] + ')'
    trie_disjunction = lambda x: 'OR(' + x[0] + ',' + x[2] + ')'
    trie_atom = lambda x: '' if x == [] else ' ' + ''.join(list(map(lambda y: str(y), x)))
    trie_atom_nothing = lambda x: '' if x == [] else ' ' + ''.join(list(map(lambda y: str(y), x)))
    trie_atom_last = lambda x: ' ' + ''.join(list(map(lambda y: str(y), x)))
    trie_module = lambda x: str(x[1])
    trie_modules = lambda x: '' if ''.join(list(map(lambda y: str(y), x))) == '' else ''.join(
        ["MODULE(", ''.join(list(map(lambda y: str(y), x))), ")\n"])
    trie_program = lambda x: ''.join(x[0]) + "" + ''.join(x[1]) + (''.join(x[2])).strip() + "\n"
    trie_list = (lambda x: foldr(lambda y, z: ' cons(' + y + ', ' + z + ')', x, 'nil'))
    trie_list_short = (lambda x: ' cons(' + x[0] + ', ' + x[2] + ')')
    trie_list_long = (lambda x: make_list(x[0], x[2]))
    trie_mlist = (lambda x: ''.join(list(map(lambda y: str(y), x[1]))))
    trie_get_fst = lambda x: x[1]
    trie_allow_word = lambda x: x != "type" and x != "module"
    trie_types = lambda x: '' if ','.join(list(map(lambda y: str(y), x))) == '' else ''.join(
        ["TYPES(", ','.join(list(map(lambda y: str(y), x))), ")\n"])
    trie_type_short = lambda x: 'type(' + x[0] + ',' + x[2] + ')'
    trie_type_long = lambda x: 'Typedef ' + x[1] + ' (' + x[2] + ')'
    trie_program_final = lambda x: '\n'.join(x)

    definition = fwd()
    identifier = fwd()
    var = fwd()
    atom = fwd()
    subatom = fwd()
    subsubatom = fwd()
    block = fwd()
    conjunction = fwd()
    disjunction = fwd()
    module = fwd()
    program = fwd()
    type = fwd()
    type_atom1 = fwd()
    type_atom2 = fwd()
    t_atom = fwd()
    t_subatom = fwd()
    t_subsubatom = fwd()
    typeid = fwd()
    mlist = fwd()
    sublist = fwd()
    ident_atom = fwd()

    sublist.define(repsep(atom | var | mlist, AND) > trie_list)

    mlist.define((LBRK & ((((atom | var | mlist) & LOGOR & var) > trie_list_short) | (
            (sublist & LOGOR & var) > trie_list_long) | sublist) & RBRK) > trie_mlist)

    definition.define(((atom & DEF & disjunction & TAIL) > trie_definition_long) |
                      ((atom & TAIL) > trie_definition_short))

    identifier.define((pred(ID, trie_allow_word, '')) > trie_identifier)

    var.define((pred(VAR, trie_allow_word, '')) > trie_var)

    typeid.define((pred(TYPEID, trie_allow_word, '')) > trie_nothing)

    atom.define((identifier & (
            rep(((LBR & (identifier | ident_atom) & RBR) > trie_get_fst) | ((LBR & subatom & RBR) > trie_atom_nothing) | subsubatom) > trie_atom_nothing)) > trie_atom_last)

    subatom.define((atom > trie_atom_nothing) |
                   (((LBR & (identifier | var | subatom | mlist ) & RBR) > trie_get_fst) > trie_atom_nothing))

    subsubatom.define((atom > trie_atom_nothing) |
                      (((identifier | var | mlist) & (rep(subsubatom) > trie_atom_nothing)) > trie_atom_nothing))

    ident_atom.define(identifier | var | ((LBR & ident_atom & RBR) > trie_get_fst))

    block.define((((LBR & disjunction & RBR) > trie_get_fst) |
                  atom) > trie_nothing)

    conjunction.define(((block & AND & conjunction) > trie_conjunction) |
                       block)

    disjunction.define(((conjunction & OR & disjunction) > trie_disjunction) |
                       (conjunction > trie_nothing))

    module.define(((MOD & identifier & TAIL) > trie_module) > trie_modules)

    program.define(((opt(module)) & (opt(type)) & (opt(rep(definition) > trie_program_final))) > trie_program)

    # t_atom.define((TYPEID & (rep(((LBR & t_subatom & RBR) > trie_atom) | t_subsubatom) > trie_atom)) > trie_atom_last)
    #
    # t_subatom.define((t_atom > trie_atom) |
    #                  (((LBR & t_subatom & RBR) > (lambda x: x[1])) > trie_atom))
    #
    # t_subsubatom.define((t_atom |
    #                      TYPEID & (rep(t_subsubatom) > trie_atom)) > trie_atom)

    type_atom1.define((((LBR & type_atom2 & RBR) > trie_get_fst) |
                       (atom | var)) > trie_nothing)

    type_atom2.define(((type_atom1 & ARR & type_atom2) > trie_type_short) |
                      (type_atom1 > trie_nothing))

    type.define(rep((TYPE & identifier & type_atom2 & TAIL) > trie_type_long) > trie_types)


if __name__ == '__main__':
    filename = sys.argv[2]
    with open(filename, 'r') as file:
        string = file.read()

    if len(sys.argv) != 3:
        print(f'use next flags:\n--atom\n--typeexpr\n'
              f'--type\n--module\n--relation\n--list\n--prog\n')
        sys.exit()
    if sys.argv[1] == '--atom':
        tmp = PrologParser.atom.parse(string)
    elif sys.argv[1] == '--typeexpr':
        tmp = PrologParser.type_atom2.parse(string)
    elif sys.argv[1] == '--type':
        tmp = PrologParser.type.parse(string)
    elif sys.argv[1] == '--module':
        tmp = PrologParser.module.parse(string)
    elif sys.argv[1] == '--relation':
        tmp = PrologParser.definition.parse(string)
    elif sys.argv[1] == '--list':
        tmp = PrologParser.mlist.parse(string)
    elif sys.argv[1] == '--prog':
        tmp = PrologParser.program.parse(string)
    else:
        print(f'use next flags:\n--atom\n--typeexpr\n'
              f'--type\n--module\n--relation\n--list\n--prog')
        sys.exit()

    if type(tmp) == Success:
        s = tmp.value
        s = re.sub(r' +', r' ', s)
        s = re.sub(r'\(\s', r'(', s)
        s = re.sub(r'\s\)', r')', s)
        s = re.sub(r',', r', ', s)
        s = re.sub(r',\s\s', r', ', s)
        print(f'Successful, see result in {filename}.out')
        with open(filename + '.out', 'w') as file:
            file.write(s)
    else:
        print(f'Smth went wrong, see result in {filename}.out')
        with open(filename + '.out', 'w') as file:
            file.write(tmp.message)
    # strings = [
    #     'type a ((((((((((((a)))->(((a)))))))))->(((((((((a)))->(((a)))))))))))).',
    #     'type a A -> ((b -> (c [a, b, c, [[a ab, s |P] | P ] |P])) -> ((a A (((d)))) -> a)).type a arf.',
    #     'module modul. type a a -> (((((b -> (c))))) -> ((a A (((d)))) -> a)).f :- ((a b)); a B c (c c [a, b, c, [[a ab, s |P] | P ] |P] c c c) (c) h g g g  g g .',
    #     'f :- ((a b)); a b c (c c Cijhn C C C) (c) h g g g  g g .',
    #     'f :- ((((a)))), b .',
    #     'f :- ((((((a B)))))); a b c ((((((c c cijhn c c c)))))) ((((c)))) (((h))) ;g  G g  g g .',
    #     'f :- a; b, c.',
    #     'type a (((((((a))) -> (((a))))))).'
    # ]
    #
    # for string in strings:
    #     tmp = PrologParser.program.parse(string)
    #     if type(tmp) == Success:
    #         s = tmp.value
    #         s = re.sub(r' +', r' ', s)
    #         s = re.sub(r'\(\s', r'(', s)
    #         s = re.sub(r'\s\)', r')', s)
    #         s = re.sub(r',', r', ', s)
    #         s = re.sub(r',\s\s', r', ', s)
    #         print(s.strip() + '\n')
    #     else:
    #         print(tmp.message)
