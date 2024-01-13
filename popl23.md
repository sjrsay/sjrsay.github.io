---
title: Higher-order MSL
layout: article
---

# Higher-Order MSL Horn Constraints

*This is an introduction to joint work with Eddie Jones and Jerome Jochems.  The full paper, which was published at POPL'23, is available [here](papers/homsl.pdf).*

This work introduces a new fragment of *higher-order* logic, and shows that it is decidable - i.e. that there is an algorithm which, given any formula in the fragment, can determine satisfiability of the formula.  It also introduces a new kind of correspondence between formulas and types, which is somewhat less superficial than the syntax-only correspondence due to Curry and Howard.  

Decidable fragments of expressive logics are often very useful because, if we can express program verification problems as formulas of the logic, then the decision procedure for the logic constitutes a method for proving the correctness of programs.  The new logic we introduce here, *Higher-order MSL* is particularly interesting because it is a higher-order logic, so it is a natural language in which to express properties of higher-order computation, such as the following.

Consider the following Haskell expression, which is featured on the Haskell.org wiki as a prototypical example of a mistake due to improper use of lazy IO for any input. 
The expression throws a runtime exception for attempting to read from a closed file handle. 
```haskell
  do  contents <- withFile "test.txt" ReadMode hGetContents
      putStrLn contents
```

This code reads the file named ``test.txt'' (line 1) and prints the contents to stdout (line 2).

The problem comes from the interaction between the lines.  The reading of the file is done using the primitive `hGetContents`, which returns the list of characters read from a handle lazily (in fact the handle is put into an intermediate *semi-closed* state, but it is not important to this example so, in the interests of simplicity, we will not model it in what follows).

The `hGetContents` action is wrapped in the `withFileS` combinator, which brackets the execution of `hGetContents` between a call to open the handle and a call to close it again.  Hence, at the point at which the contents of the file are demanded, in line 2, the file handle has already been closed as a result of leaving `withFileS`, and forcing the lazy list of characters results in attempting to read from this closed handle, resulting in an exception.

An abstraction of the behaviour of this expression, and the primitives and combinators contained therein, can be expressed in our new logic, as a set of *higher-order MSL clauses* shown below.  In principle, given the Haskell code, we could construct this set of clauses automatically -- see Naoki Kobayashi's JACM article on *Model Checking Higher-Order Programs* for a similar approach -- but this is not the focus of this work.

$$
\newcommand{\Cex}{\mathsf{V}}
\newcommand{\IsClosed}{\mathsf{Closed}}
\newcommand{\IsOpen}{\mathsf{Open}}
\newcommand{\IsSemiClosed}{\mathsf{SemiClosed}}
\newcommand{\openS}{\mathsf{open}}
\newcommand{\closeS}{\mathsf{close}}
\newcommand{\readS}{\mathsf{read}}
\newcommand{\putStrS}{\mathsf{putStrLn}}
\newcommand{\withFileS}{\mathsf{withFile}}
\newcommand{\hGetContentsS}{\mathsf{hGetContents}}
\newcommand{\openhdl}{\mathsf{o}}
\newcommand{\semiclosedhdl}{\mathsf{c}}
\newcommand{\closedhdl}{\mathsf{c}}
\newcommand{\ReadModeS}{\mathsf{ReadMode}}
\newcommand{\foreverS}{\mathsf{forever}}
\newcommand{\actionS}{\mathsf{act}}
\newcommand{\getLineS}{\mathsf{getLine}}
\newcommand{\Exists}{\mathsf{Ex}}
\newcommand{\PredS}{\mathsf{Pred}}
\newcommand{\withFileSA}{\mathsf{withFile}_1}
\newcommand{\withFileSB}{\mathsf{withFile}_2}
\newcommand{\withFileSC}{\mathsf{withFile}_3}
\newcommand{\actSA}{\mathsf{act}_1}
\newcommand{\actSB}{\mathsf{act}_2}
\newcommand{\actSC}{\mathsf{act}_3}
\newcommand{\putContS}{\mathsf{putCont}}
\newcommand{\idS}{\mathsf{id}}
\newcommand{\truetm}{\mathsf{true}}
\newcommand{\falsetm}{\mathsf{false}}
$$
$$
  \begin{align*}
    p\ [] &\implies \Exists\ p\\
    \exists y.\ p(y \mathord{:} \readS) &\implies \Exists\,p \\
    \Cex(x) &\implies \Cex(\idS\,x) \\
    \Cex(k\,x\,h) &\implies \PredS\,h\,k\,x \\
    \Cex(k\,\openhdl)  &\implies \Cex(\openS\,h\,k) \\
    \Cex(k\,\closedhdl)  &\implies \Cex(\closeS\,h\,k)\\
		\IsClosed(h)   &\implies \Cex(\readS\ h\ k) \\
		\IsOpen(h) \wedge \Exists\,(\PredS\,h\,k)  &\implies \Cex(\readS\ h\ k) \\
		\Cex(k\ ())) &\implies \Cex(\putContS\ k\ y\ h) \\
		\Cex(x\ h\ (\putContS\ k))  &\implies \Cex(\putStrS\ x\ h\ k) \\
		\Cex(\openS\ h\ (\withFileSA\ f\ k))  &\implies \Cex(\withFileS\, x\, m\, f\, h\, k) \\
		\Cex(f\ h_0\ (\withFileSB\ k)) &\implies \Cex(\withFileSA\ f\ k\ h_0) \\
		\Cex(\closeS\ h_1 (\withFileSC\ y\ k)) &\implies \Cex(\withFileSB\ k\ h_1\ y) \\
		\Cex(k\ y\ h_2) &\implies \Cex(\withFileSC\ y\ k\ h_2) \\
		\IsOpen(h) \wedge \Cex(k\ \openhdl\ \readS)  &\implies \Cex(\hGetContentsS\ h\ k) \\
		% \Cex(a\ \closedhdl\ (\foreverS\ a))  &\implies \Cex(\foreverS\ a) \\
		% \Cex(\exists x.\ k\ x\ h)  &\implies \Cex(\getLineS\ h\ k) \\
		% \Cex(\getLineS\ h\ (\actSA\ k)) &\implies \Cex(\actionS\ h\ k) \\
		% \Cex(\withFileS\ \texttt{"test.txt"}\ \hGetContentsS\ h_0\ (\actSB\ k)) &\implies \Cex(\actSA\ h_0) \\
		\Cex(\putStrS\ x\ h_3\ \idS) &\implies \Cex(\actSB\ x\ h_3) \\
		\truetm &\implies \IsOpen(\openhdl) \\
		\truetm &\implies \IsClosed(\closedhdl) 
\end{align*}
$$

It's not important to understand the precise way in which these clauses model the verification problem, but, roughly speaking, the idea is that both global state (the status of the file handle) and control flow (lazy evaluation) are represented explicitly by threading a state parameter $$h$$ and passing continuations $$k$$ respectively.  The idea is that the predicate $\Cex$ (for 'V'iolation) is true of its argument $s$ just if $s$ represents an expression that will attempt to read from a closed file handle.

The goal $\Cex(\withFileS\ \texttt{"test.txt"}\ \hGetContentsS\ \closedhdl\ (\actSB\ \idS))$ represents the verification question: does the given expression crash with a closed file-handle violation?  

The key point is that the clauses are a sound abstraction of this verification problem in the sense that: 

> *The program is safe (will not crash) 
> if there is a model of the clauses that refutes the goal.*

Since the clauses can, in principle, be generated automatically, and since there is a decision procedure for our new *higher-order MSL* logic in which they are expressed, we can overall obtain a fully-automatic procedure for solving the verification problem (though since the verification problem is undecidable, solutions will not be forthcoming in every instance).

In this case, the program is not safe and every model will affirm the goal.  In such cases one can find a resolution proof, such as that seen below.

$$
\require{bussproofs}
$$
$$
\begin{prooftree}
              \AxiomC{}
							\UnaryInfC{$\IsOpen(\openhdl)$}
                          \AxiomC{}
													\UnaryInfC{$\IsClosed(\closedhdl)$} 
													\UnaryInfC{$\Cex(\readS\ \closedhdl\ (\putContS\ \idS))$}
													\UnaryInfC{$\Cex(\putStrS\ \readS\ \closedhdl\ \idS)$}
												\UnaryInfC{$\Cex(\actSB\ \readS\ \closedhdl)$}
											\UnaryInfC{$\Cex(\withFileSC\ \readS\ \actSB\ \closedhdl)$}  
									\UnaryInfC{$\Cex(\closeS\ \openhdl\ (\withFileSC\ \readS\ \actSB))$}
								\UnaryInfC{$\Cex(\withFileSB\ \actSB\ \openhdl\ \readS)$}
							\BinaryInfC{$\IsOpen(\openhdl) \wedge \Cex(\withFileSB\ \actSB\ \openhdl\ \readS)$}
						\UnaryInfC{$\Cex(\hGetContentsS\ \openhdl\ (\withFileSB\ \actSB))$}
					\UnaryInfC{$\Cex(\withFileSA\ \hGetContentsS\ \actSB \ \openhdl)$}
				\UnaryInfC{$\Cex(\openS\ \closedhdl\ (\withFileSA\ \hGetContentsS))$}
			\UnaryInfC{$\Cex(\withFileS\ \texttt{``test.txt''}\ \ReadModeS\ \hGetContentsS\ \closedhdl\ \actSB)$}
\end{prooftree}
$$

## The Monadic, Shallow, Linear Fragment

Now, let's take a closer look at what our new logic (fragment) looks like.  The starting point is the well-known Monadic Shallow Linear (MSL) fragment of *first-order* Horn clauses, which was discovered independently in the automated reasoning community (by Christoph Weidenbach) and in the program analysis community (by Flemming Nielson, Hanne Riis Nielsen and Helmut Seidl).  

As you may know, a first-order Horn clause is a clause of first-order logic containing at most one positive literal.  Every such clause can be written in one of two ways:

* $P_1(\vec{s_1}) \wedge \cdots{} \wedge P_k(\vec{s_k}) \implies Q(\vec{t})$
* or, $P_1(\vec{s_1}) \wedge \cdots{} \wedge P_k(\vec{s_k}) \implies \falsetm$

where each $P_i$ and $Q$ first-order predicate symbols, and each $\vec{s_i}$ and $\vec{t}$ a tuple of first-order terms.  The former are known as *definite clauses* and the latter are known as *goal clauses*, the part to the left of the implication is the *body* of the clause and the part to the right is the *head*.  Each application of a predicate is called an *atom* (atomic formula).

Unrestricted first-order Horn clauses have an undecidable satisfiability problem - just think to their use as the basis of logic programming languages like Prolog.  However, the MSL fragment makes certain, quite natural, restrictions to the syntactical shape of the clauses that restores decidability.  

1. Each predicate symbol is __M__*onadic*, i.e. it has exactly one argument.  Thus, the tuples of terms above are all of length 1.
    * E.g. $$P(s)$$ but not $$P(s_1,s_2)$$.
2. Each head is __S__*hallow*, i.e. the single argument of $Q$ is either a variable or is a function symbol applied to a tuple of variables.
    * E.g. $$Q(x)$$ or $$Q(f(x, y))$$ but not $Q(f(g(x),y))$.
3. Each head is __L__*inear*, i.e. the term $t$ contains at most occurrence of any given variable.
    * E.g. $$Q(f(x, y))$$, but not $Q(f(x,x))$.

Note, apart from the requirement for monadic predicates, there is no restriction on the bodies of clauses at all.  The following set of clauses over the successor $\mathsf{s}$, 0 and $\mathsf{mul}$ are MSL:
$$
\newcommand{\Odd}{\mathsf{O}}
\newcommand{\Ev}{\mathsf{E}}
\newcommand{\sc}{\mathsf{s}}
\newcommand{\mult}{\mathsf{mul}}
$$

$$
\begin{array}{rcl}
  \truetm &\implies& \Ev(0)\\
  \Ev(x) &\implies& \Odd(\sc(x))\\
  \Odd(x) &\implies& \Ev(\sc(x))\\
  \Odd(x) \wedge \Odd(y) &\implies& \Odd(\mult(x,y))\\
  \Odd(\mult(\sc(x),\sc(y))) &\implies& \Ev(\mult(x,y))\\
  \Ev(x) \wedge \Odd(x) &\implies& \falsetm
\end{array}
$$

## MSL and Finite Automata

Among all the different kinds of MSL clauses we can single out a subset that are particularly well behaved.  These are sometimes called the $$automaton$$ clauses.  Automaton clauses additionally restrict the body so that atoms must have shape $P(x)$ - i.e. the single argument of the monadic predicate is just a variable.  Moreover, this variable $x$ is required to also appear in the head.

Of the clauses above, the first 4 are automaton, the final two are not.  The penultimate clause is not because the only atom in the body is an application of $P$ to a compound term $\mult(\sc(x),\sc(y))$.  The last clause is not because, although the atoms have the correct shape, their subject $x$ does not occur in the head of the clause.

$$
\newcommand{\Cons}{\mathsf{cons}}
\newcommand{\Nil}{\mathsf{nil}}
$$

Sets of automaton clauses can be understood as a kind of finite automata called *alternating tree automata*.  These are finite automata that run over trees (rather than words) and which have universal non-determinism as well as the usual existential non-determinism.  To illustrate let us consider the transition function of a simple (top-down) tree automaton that accepts Boolean lists (trees over $\Cons$, $\Nil$, 0 and 1).  We consider all states to be accepting.

$$
  \begin{array}{rcl}
    q_0 &\overset{\Nil}{\longmapsto}& \\
    q_0 &\overset{\Cons}{\longmapsto}& q_1,\, q_0\\
    q_1 &\overset{0}{\longmapsto}& \\
    q_1 &\overset{1}{\longmapsto}& \\
  \end{array}
$$

Intuitively, the automaton starts processing a given tree (Boolean list) starting from the root and reading in one symbol at a time.  Then, the first transition says that from state $q_0$ the automaton can read a leaf labelled with the empty list $\Nil$ and then terminate the processing of that branch.  The second says that, from state $q_0$ the automaton will read a $\Cons$ and then continue reading the head of the list in state $q_1$ and the tail in state $q_0$.  The final two transitions say that the automaton will read in either a 0 or a 1 from state $q_1$ and then terminate the processing of that branch.

Thus, the trees accepted from $q_1$ are just the Booleans (trees of exactly one node) $0$ and $1$, and the trees accepted from state $q_0$ are therefore all lists of Booleans.
$$
\newcommand{\BList}{\mathsf{BList}}
\newcommand{\Bool}{\mathsf{Bool}}
$$

The same tree automaton can be rendered as a set of automaton clauses, if we identify state $q_0$ with a predicate $\BList$ and state $q_1$ with a predicate $\Bool$.  The idea is to think of a state as the set of all trees that the automaton would accept if started in that state, i.e. a monadic predicate on trees.

$$
  \begin{array}{rcl}
    \truetm &\implies& \BList(\Nil)\\
    \Bool(x) \wedge \BList(xs) &\implies& \BList(\Cons(x,xs))\\
    \truetm &\implies& \Bool(0)\\
    \truetm &\implies& \Bool(1)\\
  \end{array}
$$

That this example is just a simple, deterministic tree automaton shows up in the fact that the clause heads are disjoint and every variable that occurs in a head occurs exactly once in the corresponding body.

Due to this close relationship with automata, automaton clauses have excellent algorithmic properties.  It is straightforward to decide if a given set of automaton clauses has a model because it can be set up in such a way that it reduces to checking emptiness of the automaton.

Remarkably, Weidenbach showed that every set of MSL clauses is equivalent to a set of automaton clauses, in the sense that one is satisfiable iff the other is.  Thus, it is possible to determine the satisfiability of a set of MSL clauses by first transforming them into an equivalent set of automaton clauses and then checking emptiness of the automaton.

Moreover, the transformation from MSL to automaton is very neat.  It is just a form a clausal resolution in which exactly one of the two resolved clauses is already an automaton clause.  If we return to our previous example and take one of the final two, non-automaton clauses, say:

$$
  \Odd(\mult(\sc(x),\sc(y))) \implies \Ev(\mult(x,y))
$$

then we can resolve it with an automaton clause, that is, unify the head of an automaton clause to an atom in the body of the non-automaton clause to generate a new clause in which that atom is replaced by the body of the automaton clause (under appropriate substitution).  Here the body of the above clause will unify with the head of the following automaton clause:

$$
  \Odd(x) \wedge \Odd(y) \implies \Odd(\mult(x,y))
$$

since the replacment, $x \mapsto \sc(x)$ and $y \mapsto \sc(y)$, makes the head of this automaton clause $\Odd(\mult(\sc(x),\sc(y)))$ identified with an atom in the body of the non-automaton clause.  Their resolution results in a new clause:

$$
\Odd(\sc(x)) \wedge \Odd(\sc(y)) \implies \Ev(\mult(x,y))
$$

And, because of the strict shape of automaton clauses, in which the body atoms are predicates applied to a single variable, the new clause will always be "more automaton" (e.g. the terms in the body will become shallower) than the original non-automaton clause.  

Since there are only finitely many automaton clauses over a given signature of function and predicate symbols (up to variable renaming), it follows that iterating this process will eventually stop generating new clauses, and the resulting set of automaton clauses is guaranteed to be equi-satisfiable with the original.

## MSL at Higher Order

The aim of this work is to extend the MSL fragment to higher-orders, whilst retaining its excellent algorithmic properties (in particular the decidability of satisfiability).  However, there is a question over what we mean by "higher-orders".  

One possibility is to retain first-order predicates, but allow higher-order term formation.  In other words, predicates would still only apply to arguments of ground type, but those ground type terms could be formed as the application of e.g. higher-order functions.  For example $P(\mathsf{map}\,f\,xs)$ is not allowed in first-order MSL because $\mathsf{map}$ is a higher-order function, but this would now be allowed, although an application of a predicate to a non-ground type subject like $P(\mathsf{map}\,f)$ would not.  

Another possibility is to retain first-order terms, but allow higher-order predicates - that is, predicates whose subjects are also predicates (of a lower order).  So $P(Q)$ would be allowed.  Here, it is worthwhile to mention that MSL effectively allows for predicates that take multiple arguments because one can simulate this with a monadic predicate that takes a single tuple (constructed using a tuple constructor function) as its only argument (but this, of course, has implications when it comes to asserting such an application in the head - the force of the monadic requirement must be felt eventually).  Thus, we could allow even $P\,Q\,R$, partial applications of curried higher-order predicates and so on; which are obviously out of scope in first-order MSL.  However, any terms would still be first-order.

$$
\newcommand{\HOMSL}{\mathsf{HOMSL}}
\newcommand{\MSL}{\mathsf{MSL}}
$$

These two possibilities lead to the following classification of fragments.  The family of fragments $\MSL(n)$, for $n$ drawn from $\mathbb{N} \cup \{\omega\}$, requires predicate arguments to be of ground type, but the terms out of which the arguments are constructed can be of any type up to order $n-1$.  The family of fragments $\HOMSL(n)$ allows for predicates with arguments that can themselves be predicates (more generally relations) of any type up to order $n-1$.  We regard $\omega = \omega - 1$ and $0$ as a prohibition on arguments (i.e. one may not construct function types).

* $\MSL(0)$ is Datalog: predicates are first order and their subjects are (nullary) constants.
* $\MSL(1)$ is the first-order MSL fragment.
* $\MSL(\omega)$ is the first of the two higher-order extensions described above: we have first-order predicates whose subjects are trees constructed from an arbitrary higher-order signature.
* $\HOMSL(0)$ is higher-order Datalog, as studied by, e.g. Charalambidis, Nomikos and Rondogiannis. 
* $\HOMSL(1)$ is the second of the two higher-order extensions described above: we have higher-order predicates over trees defined using only first-order tree constructors.
* $\HOMSL(\omega)$ allows for higher-order extensions in both directions.

In the paper, we show that actually the latter three entries of this classification can be collapsed into $\MSL(\omega)$, essentially by considering higher-order predicates as higher-order Boolean-valued functions and then representing them in a uniform way as terms.  You may notice that the example given at the start of this article is all expressed in $\MSL(\omega)$ because the subject of each predicate is a term of ground type, but that term is constructed using e.g. higher-order functions (such as the continuations).

Thus, the main challenge of the work is to come up with a decision procedure that will work for this higher-order logic, $\MSL(\omega)$.  

## Higher-order Automaton Clauses

Ideally, we would like a decision procedure that is as neat as the one for $\MSL(1)$, in which we repeatedly apply resolution in order to obtain clauses that are closer and closer to a given canonical form (like the first-order automaton clauses).  However, the fact that we now have atoms containing higher-order variables is a huge problem for this approach.

There is a higher-order analogue of the resolution rule (which also forms the core of a refutationally complete calculus for higher-order constrained Horn clauses studied by Luke Ong and Dominik Wagner):

$$
  \begin{prooftree}
    \AxiomC{$G \wedge R\ \vec{s} \implies A$}
    \AxiomC{$G' \implies R\ \vec{y}$}
    \BinaryInfC{$G \wedge G'[\vec{s}/\vec{y}] \implies A$}
  \end{prooftree}
$$

This higher-order rule has exactly the same structure as the standard first-order rule (for Horn clauses).  However, as we shall describe below, this form of resolution on its own does not lend itself to a decision procedure for $\MSL(\omega)$.

In the higher-order case when we apply this form of resolution, but restricted in such a way that the side premise must be already automaton, there is *no guarantee* that the newly generated clause is, in some sense, closer to automaton than the main premise.  In particular, when the selected negative literal (i.e. the atom in the body of the non-automaton clause) is headed by a variable, which is only possible in the higher-order case, this spells trouble.

Consider, for example, the following resolution inference.

$$
  \begin{prooftree}
  \AxiomC{$\mathsf{P}(x_1\ (\mathsf{f}\ \mathsf{a}\ x_2)) \implies \mathsf{Q}(\mathsf{g}\ x_1\ x_2)$}
  \AxiomC{$\mathsf{R}(y_2) \wedge \mathsf{S}(y_2) \implies \mathsf{P}(\mathsf{h}\ y_1\ y_2)$}
  \BinaryInfC{$\mathsf{R}(\mathsf{f}\ \mathsf{a}\ x_2) \wedge \mathsf{S}(\mathsf{f}\ \mathsf{a}\ x_2) \implies \mathsf{Q}(\mathsf{g}\ (\mathsf{h}\ y_1)\ x_2)$}
  \end{prooftree}
$$

As in the first-order case, the body of the clause in the conclusion *can* be viewed as closer to our automaton solved form, *but* the head of the clause is further away from automaton form. *In fact, the clause has departed the MSL fragment completely since it no longer has a shallow head!*  This is a significant problem because, by inspection, further resolution inferences with this non-MSL clause as the main premise can only produce clauses with a head of the same or even greater depth.

However, resolving on clauses where the selected negative literal is headed by a variable appears inescapable if we insist one of the premises of each resolution inference to be automaton.  In the following example, we can obtain a contradiction by resolution, but the only automaton clause is the first one, so there is no choice but to resolve the first and second, which leads to a deep head as above.

$$
  \begin{array}{rcl}
  \truetm &\implies& \mathsf{P}(\mathsf{h}\ y_1\ y_2) \\
  \mathsf{P}(x_1\ (\mathsf{f}\ \mathsf{a}\ x_2)) &\implies& \mathsf{Q}(\mathsf{g}\ x_1\ x_2) \\
  \mathsf{Q}(\mathsf{g}\ (\mathsf{h}\ z)\ \mathsf{a}) &\implies& \mathsf{false}
  \end{array}
$$

Our solution to this problem is to radically rethink the form of automaton clauses in the higher-order setting.  

We observe that a clause with a deep head, like: 

$\mathsf{R}(\mathsf{f}\ \mathsf{a}\ x_2) \wedge \mathsf{S}(\mathsf{f}\ \mathsf{a}\ x_2) \implies \mathsf{Q}(\mathsf{g}\ (\mathsf{h}\ y_1)\ x_2)$ 

can be thought of as a clause with a shallow head, so long as we include an additional constraint $x_1 = h\ y_1$ in the body: 

$\mathsf{R}(\mathsf{f}\ \mathsf{a}\ x_2) \wedge \mathsf{S}(\mathsf{f}\ \mathsf{a}\ x_2) \wedge x_1 = h\ y_1 \implies \mathsf{Q}(\mathsf{g}\ x_1\ x_2)$

Of course, allowing arbitrary equational constraints (and especially at higher type) in the body will lead us immediately outside of a decidable fragment, so we cannot state such constraints directly.

Rather, we ask only that the new higher-order variable $x_1$ ``behave like'' $h\ y_1$.
Since $x_1$ and $h\ y_1$ are both functions, the most obvious route to making this precise is to ask that they behave similarly on similar inputs.

Moreover, there is a clear way to define similar, because we are only able to observe the behaviour of terms through the lens of our stock of predicate symbols. For example, if we only had a single predicate $P$ then all terms $s$ for which $P(s)$ is true are alike, we have no mechanism to write a constraint that distinguishes them.

Hence, to ask that $x_1$ behaves as $h\ y_1$ is to ask that $x_1$ satisfies: 

$\forall y_2.\ R(y_2) \wedge S(y_2) \implies P(x_1\ y_2)$ 

Clearly, $h\ y_1$ is an instance of $x_1$ that satisfies this constraint and, we claim, $\MSL(\omega)$ cannot distinguish between $h\ y_1$ and any other $x_1$ that also satisfies it.

Incorporating this leads to a kind of abductive inference, in which the clause in the conclusion additionally includes an atom of this shape (asserting the equivalence between some variable $x_1$ and some application $h\,y$):

$$
  \begin{prooftree}
  \AxiomC{$\mathsf{P}(x_1\ (\mathsf{f}\ \mathsf{a}\ x_2)) \implies \mathsf{Q}(\mathsf{g}\ x_1\ x_2)$}
  \AxiomC{$\mathsf{R}(y_1) \wedge \mathsf{S}(y_2) \implies \mathsf{P}(\mathsf{h}\ y_1\ y_2)$}
  \BinaryInfC{$\mathsf{R}(\mathsf{f}\ \mathsf{a}\ x_2) \wedge \mathsf{S}(\mathsf{f}\ \mathsf{a}\ x_2) \wedge (\forall y_2.\ \mathsf{R}(y_2) \wedge \mathsf{S}(y_2) \implies \mathsf{P}(x_1\ y_2)) \implies \mathsf{Q}(\mathsf{g}\ x_1\ x_2)$}
  \end{prooftree}
$$

Of course, we have still ended up outside the MSL fragment, but the additional power required to state this form of constraint on $x_1$ seems much less dangerous: this nested implication is none other than an MSL clause itself -- the head is shallow and linear -- and, moreover, its body is already in the correct form to be automaton.  In fact, in the paper, we show that this form of nested clause is exactly the generalisation of automaton clause that we need in the higher-order setting.  We give a decision procedure based on saturation under resolution with these kinds of nested automaton clauses as the canonical forms.

## Higher-order Automata, Clauses and Types

Higher-order automaton clauses are, like their first-order counterparts, extremely natural and very well-behaved.  There is a sense in which they correspond to *higher-order* finite automata, but perhaps more interesting is their relationship with types.  After all, it is well known by those in the higher-order program verification community that *types* are a smooth generalisation of automata (see particularly the work of Naoki Kobayashi).  For example, the finite tree automaton whose transition function is described above can be equivalently given as a set of first-order typings for the function symbols, in which each state is understood as a base type and we have that a term tree has type $q_0$ iff it can be accepted from state $q_0$:

$$
  \begin{align*}
    \mathsf{nil} &: q_0 \\
    \mathsf{cons} &: q_1 \times q_0 \to q_0 \\
    0 &: q_1\\
    1 &: q_1 
  \end{align*}
$$

Higher-order automaton clauses correspond to higher-order typings, with the nesting in the higher-order clauses precisely in alignment with the nesting of arrows in higher types.  For example, the following higher-order automaton clause, involving predicates $\mathsf{P}$, $\mathsf{Q}$, $\mathsf{ListP}$ and $\mathsf{ListQ}$:

$$
  \begin{array}{c}
    \forall f\,xs.\, (\forall x.\, \mathsf{P}\,x \implies \mathsf{Q}\,(f\,x)) \wedge \mathsf{ListP}\,xs \implies \mathsf{ListQ}\,(\mathsf{map}\,f\,xs)
  \end{array}
$$

corresponds to the following higher-order typing for $\mathsf{map}$ over base types $\mathsf{P}$, $\mathsf{Q}$, $\mathsf{ListP}$ and $\mathsf{ListQ}$:

$$
  \mathsf{map} : (P \to Q) \to \mathsf{ListP} \to \mathsf{ListQ}
$$

Higher-order automaton clauses may have many atoms in the body whose subject is the same variable, and so, in general, the correspondence is with *intersection types*.  For example, the following higher-order automaton clause:

$$
  \forall f\,y.\, (\forall x.\, \Ev\,x \implies \Odd\,(f\,x)) \wedge (\forall x.\, \Odd\,x \implies \Ev\,(f\,x)) \wedge \Odd\,y \implies \Odd\,(g\,f\,y) 
$$

corresponds to the following higher-order typing:

$$
  g : (\Ev \to \Odd) \wedge (\Odd \to \Ev) \to \Odd \to \Odd
$$

This is a correspondence between formulas and types rather different from that credited to Curry and Howard.  The Curry-Howard correspondence is somewhat superficial - in the sense that it concerns only syntax.  Here the correspondence is about semantics.  For every intersection type over a certain signature of base types, there is a corresponding higher-order automaton clause that describes its semantics - as a predicate, or collection of values - and, conversely, every higher-order automaton clause describes the semantics of some intersection type.  

We exploit this correspondence to show that the satisfiability problem for $\MSL(\omega)$ and the higher-order model checking (safety) problem are interreducible, but I won't go into the details here.  

This is a nice result because HORS model checking, although influential, is a set of techniques for solving a somewhat exotic problem.  The safety version of the problem asks to decide if the value tree determined by a certain kind of higher-order grammar is accepted by a Büchi tree automaton with a trivial acceptance condition.  Thanks to the results of this paper, this form of higher-order model checking can be located more simply as "a group of decision procedures for the MSL fragment".  We hope this will make this topic more accessible to the wider verification community, since monadic, shallow, and linear restrictions are well understood even by non-experts on higher-order program verification.  

In first-order automated program verification there is a consensus around first-order logic as foundation, to the benefit of the field.  On the one hand, ideas from first-order logic, such as interpolants, the Horn fragment, abduction, resolution, and so on have found an important place in automated verification.  On the other, first-order logic provides a common vocabulary with which to understand the automated verification landscape *conceptually*, and locate different technologies.  For example, predicate abstraction, although a complex and varied set of techniques, may be located in this landscape as a set of algorithms for synthesizing the strongest inductive invariant expressible by a fixed set of predicates.  

However, higher-order automated program verification comprises a disparate collection of formalisms: refinement types, higher-order grammars and automata, higher-order fixpoint logic, and many others.  Moreover, the procedures involved are often bespoke and difficult to relate to techniques that are standard in first-order verification.

This paper is part of a larger effort to establish an analogous foundation for higher-order automated program verification based on higher-order logic, which began with my [POPL'18](https://research-information.bris.ac.uk/files/142259264/popl18_p253.pdf) paper, with Luke Ong and Toby Cathcart Burn, that introduced higher-order constrained Horn clauses.  Here we have shown that a standard technique from first-order automated reasoning, namely saturation under resolution, is effective at higher order, and even forms a decision procedure for the higher-order extension of MSL.  Furthermore, in combination with our correspondence between intersection types and higher-order automaton clauses, this sets up a pattern for understanding type-based approaches to verification more generally. 