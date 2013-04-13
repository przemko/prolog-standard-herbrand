% herbrand.pl
%
% Generating elements of the Herbrand's universe and the Herbrand's
% base.
%
% Author: Przemyslaw Kobylanski <przemko@pwr.wroc.pl>
%
% FORMULA  ::= '[]' | '[' CLAUSES ']'
% CLAUSES  ::= CLAUSE | CLAUSE ',' CLAUSES
% CLAUSE   ::= '[]' | '[' LITERALSE ']'
% LITERALS ::= LITERAL | LITERAL ',' LITERALS
% LITERAL  ::= ATOM | '\+' ATOM
% ATOM     ::= SYMBOL | SYMBOL '(' TERMS ')'
% TERMS    ::= TERM | TERM ',' TERMS
% TERM     ::= VARIABLE | SYMBOL | SYMBOL '(' TERMS ')'
% VARIABLE ::= identifier starting with an upper case letter
% SYMBOL   ::= identifier starting with an lower case letter

:- module(herbrand,
	  [
	   signature/2,
	   herbrand_universe/2,
	   herbrand_base/2
	  ]).

% signature(+Formula, -Signature) if
%   Signature is a signature for the given Formula (set of clauses)
%
% Examples:
% ?- signature([[nat(a)], [nat(s(X)), \+nat(X)]], S).
% S = [pred(nat/1), fun(a/0), fun(s/1)].
% ?- signature([[append([], X, X)], [append([X | L1], L2, [X | L3]),
%                                    \+append(L1, L2, L3)]], S).
% S = [pred(append/3), fun([]/0), fun('.'/2)].
%
signature(Clauses, Signature) :-
	sig(Clauses, [], S),
	(   member(fun(_/0), S)
	->  Signature = S
	;   Signature = [fun(a/0) | S]).

sig([], SIG, SIG).
sig([C | L], SIG, SIG2) :-
	sig2(C, SIG, SIG1),
	sig(L, SIG1, SIG2).

sig2([], SIG, SIG).
sig2([A | L], SIG, SIG2) :-
	sig3(A, SIG, SIG1),
	sig2(L, SIG1, SIG2).

sig3(\+ A, SIG, SIG1) :-
	!,
	sig4(A, SIG, SIG1).
sig3(A, SIG, SIG1) :-
	sig4(A, SIG, SIG1).

sig4(A, SIG, SIG2) :-
	A =.. [Pred | Args],
	length(Args, N),
	insert_pred(SIG, Pred/N, SIG1),
	sig5(Args, SIG1, SIG2).

sig5([], SIG, SIG).
sig5([A | L], SIG, SIG2) :-
	sig6(A, SIG, SIG1),
	sig5(L, SIG1, SIG2).

sig6(X, SIG, SIG) :-
	var(X), !.
sig6(T, SIG, SIG2) :-
	T =.. [F | L],
	length(L, N),
	insert_fun(SIG, F/N, SIG1),
	sig5(L, SIG1, SIG2).

insert_pred([], P/N, [pred(P/N)]).
insert_pred([pred(P/N) | L], P/N, [pred(P/N) | L]) :-
	!.
insert_pred([A | L1], P/N, [A | L2]) :-
	insert_pred(L1, P/N, L2).

insert_fun([], F/N, [fun(F/N)]).
insert_fun([fun(F/N) | L], F/N, [fun(F/N) | L]) :-
	!.
insert_fun([A | L1], F/N, [A | L2]) :-
	insert_fun(L1, F/N, L2).

% herbrand_universe(+Signature, -GroundTerm) if
%   GroundTerm is an element of the Herbrand's Universe for the given
%   Signature
%
% Example:
% ?- herbrand_universe([fun(a/0), fun(f/1), fun(g/2)], X).
% X = a ;
% X = f(a) ;
% X = g(a, a) ;
% X = f(f(a)) ;
% X = f(g(a, a)) ;
% X = g(a, f(a)) ;
% X = g(a, g(a, a)) ;
% X = g(f(a), a) ;
% X = g(g(a, a), a) ;
% X = g(f(a), f(a)) ;
% X = g(f(a), g(a, a)) ;
% X = g(g(a, a), f(a)) ;
% X = g(g(a, a), g(a, a)) ;
% ...
%
herbrand_universe(Signature, GroundTerm) :-
	member(fun(_/N), Signature),
	N > 0, !,
	nat(I),
	hh(I, Signature, GroundTerm).
herbrand_universe(Signature, Constant) :-
	member(fun(Constant/0), Signature).

h(I, SIG, C) :-
	I >= 0,
	member(fun(C/0), SIG).
h(I, SIG, T) :-
	I > 0,
	I1 is I-1,
	member(fun(F/N), SIG),
	N > 0,
	length(L, N),
	T =.. [F | L],
	h2(L, I1, SIG).

hh(0, SIG, C) :-
	member(fun(C/0), SIG).
hh(I, SIG, T) :-
	I > 0,
	I1 is I-1,
	I2 is I-2,
	member(fun(F/N), SIG),
	N > 0,
	length(L, N),
	T =.. [F | L],
	split(L, L1, L2),
	L1 \= [],
	hh2(L1, I1, SIG),
	h2(L2, I2, SIG).

h2([], _, _).
h2([T | L], I, SIG) :-
	h(I, SIG, T),
	h2(L, I, SIG).

hh2([], _, _).
hh2([T | L], I, SIG) :-
	hh(I, SIG, T),
	hh2(L, I, SIG).

split([], [], []).
split([A | L], L1, [A | L2]) :-
	split(L, L1, L2).
split([A | L], [A | L1], L2) :-
	split(L, L1, L2).

% herbrand_base(+Signature, -GroundAtom) if
%   GroundAtom is an element of the Herbrand's Base for the given
%   Signature
%
% Example:
% ?- herbrand_base([pred(p/2), fun(a/0), fun(f/1), fun(g/2)], X).
% X = p(a, a) ;
% X = p(a, f(a)) ;
% X = p(a, g(a, a)) ;
% X = p(f(a), a) ;
% X = p(g(a, a), a) ;
% X = p(f(a), f(a)) ;
% X = p(f(a), g(a, a)) ;
% X = p(g(a, a), f(a)) ;
% X = p(g(a, a), g(a, a)) ;
% X = p(a, f(f(a))) ;
% X = p(f(a), f(f(a))) ;
% X = p(g(a, a), f(f(a))) ;
% X = p(a, f(g(a, a))) ;
% X = p(f(a), f(g(a, a))) ;
% X = p(g(a, a), f(g(a, a))) ;
% X = p(a, g(a, f(a))) ;
% ...
%
herbrand_base(Signature, GroundAtom) :-
	member(fun(_/M), Signature),
	M > 0, !,
	nat(I),
	I1 is I-1,
	member(pred(P/N), Signature),
	length(L, N),
	GroundAtom =.. [P | L],
	split(L, L1, L2),
	L1 \= [],
	hh2(L1, I, Signature),
	h2(L2, I1, Signature).
herbrand_base(Signature, GroundAtom) :-
	member(pred(P/N), Signature),
	length(L, N),
	GroundAtom =.. [P | L],
	h2(L, 0, Signature).



% nat(-N) if
%   N is a natural number
%
nat(0).
nat(N) :-
	nat(N1),
	N is N1+1.






