---
title: Ill-Typed Programs Don't Evaluate
layout: article
---

# Ill-Typed Programs Don't Evaluate

*The following is a slightly extended version of my POPL'24 talk, introducing joint work with Charlie Walpole.  You can find the long, arxiv version of the paper [here](https://arxiv.org/abs/2307.06928).*

$$
\newcommand{\natty}{\mathsf{Nat}}
\newcommand{\consty}{\mathsf{Cons}}
\newcommand{\nilty}{\mathsf{Nil}}
\newcommand{\okty}{\mathsf{Ok}}
\newcommand{\onlyto}{\mathrel{>\!\!\!-}}
$$

In a traditional type system, when a program is typable, then there is a guarantee that the program will be free of certain class of runtime errors.  But, when a program is untypable, there are no guarantees, it could be that the program really is incorrect: it will go wrong if someone abuses it in just the right way at runtime, but it could also be that the program is correct, it's just that the type system can't "see" it, the formal system is not expressive enough to prove the correctness property. And when a program gets rejected for being untypable, it's up the programmer to invest effort into finding out which of these two cases it is.  Now, for familiar, mainstream type systems, this is not too onerous, but for some of the highly sophisticated, highly complex type systems we see at POPL each year, I think it can be a serious barrier.

We looked at this, and we were inspired by the explosion of interest in program logics for so-called incorrectness reasoning, popularised, of course by Peter O'Hearn's incorrectness logic.  So, we set out to see what it could look like to do incorrectness reasoning in a type system - in other words, a notion of type system that can give guarantees also when programs are incorrect.  And, what we are proposing is really a fundamental new extension to the *notion* of type system.  So, I think you will find this work interesting, even if you don't care about incorrectness reasoning.

This new understanding of type systems actually comes about very naturally if, as is quite common, we consider a type system as a kind of proof system.  

$$
  x_1:A_1,\,\ldots,\,x_n:A_n \vdash M:B
$$

If we think of a type system as a kind of a proof system, then the purpose is to justify judgements: under some assumptions on the types of its free variables, the term (or program expression) $M$ is assigned the type $B$.  From the proof system point of view then, we have these hypothetical statements, or sequents, and the formulas out of which we build them are typings, they have shape $M:A$.   

Something that is clear from this view is that, unlike more traditional proof systems, say for first-order logic, type systems bake-in a fundamental asymmetry: although we can conclude an arbitrary atomic formula $M:B$, we may only assume atomic formulas that have a specific shape, namely variable : type.  It's clear how this restriction evolved when we think of type systems as a means to define what constitutes valid syntax, but when we think of a type system rather as a mechanism for proving properties of programs, it raises a question - why do we persist with it?  Semantically, we know what an arbitrary formula like $N:A$ means, $N$ evaluates to a value of type $A$, so a hypothetical statement predicated upon such a formula makes sense, semantically.  

Well, in our paper we show that removing this restriction leads to a rich, new kind of type theory, which is natural and, moreover, provides a foundation for a kind of incorrectness reasoning.

$$
  N_1:A_1,\,\ldots,\,N_n:A_n \vdash M:B
$$

Our two-sided judgements can make assumptions about *arbitrary* typing formulas, $N_i:A_i$ not only variable typings.  Semantically, we will work with CBV, and so the meaning is an obvious generalisation of the meaning of a traditional CBV typing judgement, namely "if $N_1$ evaluates to a value of type $A_1$ and ... and $N_k$ evaluates to a value of type $A_k$, then either $M$ evaluates to a value of type $B$ or $M$ diverges".

For example, in a simple CBV PCF-like system with a single base type $\natty$, we can state that:

$$
  (\lambda x.\,x)\,y : \natty \vdash y : \natty
$$

i.e. that "if the identity applied to some variable y is a natural number, then y must be a natural number".  Along the same lines, we can state:

$$
  \mathsf{ifz}\, z\, \mathsf{then}\, M \,\mathsf{else}\, N : \natty \vdash z:\natty
$$

which, for any terms M and N, says that, whenever this conditional, which tests if some variable z is zero, evaluates to a natural number, then z must be a natural number too.

Of course, we do not lose anything by making typings first-class objects in this way, we can still reason about compound terms on the right of the turnstile.  Since from the first of these hypotheses below we can deduce that y is a nat and from the second of these we can deduce z is a nat, so y + z must be a nat:

$$
  (\lambda x.\,x)\,y : \natty,\; \,\mathsf{ifz}\, z \,\mathsf{then}\,M\,\mathsf{else}\, N : \natty \vdash y + z : \natty
$$

If we have a more sophisticated collection of base types, as is found in some of these more sophisticated systems we see published at POPL, we can express more interesting 2-sided judgements.  For example, in their POPL'94 paper, Aiken, Wimmers and Lakshman used a type theory in which data constructors can be lifted to the type level (and I followed them in my [POPL'21](https://research-information.bris.ac.uk/files/265849562/3434336.pdf) paper, which traded-off expressive power for a linear-time complexity guarantee).  So there is, for example, a type $\consty{}(A,B)$ that is inhabited by all terms of shape $\mathsf{Cons}(M,N)$ whose head $M$ is of type $A$ and whose tail $N$ is of type $B$, and a type $\nilty$ containing just the empty list.  For example, the list $[1,2,3]$ has the type: 

$$
  [1,2,3] : \consty(\natty,\,\consty(\natty,\,\consty(\natty,\,\nilty)))
$$

which says that it is a cons whose head is a nat and whose tail is a cons, whose head is a nat and whose tail is a cons, whose head is a nat and whose tail is the empty list.

With these data constructor types we can state that this inexhaustive match - it extracts the head of a non-empty list and crashes otherwise - if it evaluates to a value of some type $a$, then the scrutinee $xs$ must be a cons which, moreover, has head of type $a$.

$$
  \begin{array}{l}\mathsf{match}\, xs \,\mathsf{with}\\\ \ \mathsf{Cons}(y,ys) \mapsto y\end{array} : a \vdash xs : \consty{}(a, Ok) 
$$

The tail has type $\okty$, which is our top type (so here it means a tail of "some value").  I'll say something about this later.

Two-sided type judgements also dispense with the restriction that there must be exactly one formula on the right of the turnstile, with multiple formulas understood disjunctively.  So, it follows that e.g. when this inexhaustive match evaluates to a value of type $a$, then *either* $xs$ is a cons with head of type $a$ *or* $y$ is a nat.

$$
  \begin{array}{l}\mathsf{match}\, xs \,\mathsf{with}\\\ \ \mathsf{Cons}(y,ys) \mapsto y\end{array} : a \vdash xs : \consty{}(a, Ok),\,y:\natty
$$

An empty right hand side amounts to refuting the consistency of the formulas on the left -- the empty disjunction is false.  For example, we can prove that:

$$
  x:\natty \to \natty,\; \mathsf{head}\,(\mathsf{Cons}\,(x,\,\mathsf{Nil})) : \natty \vdash
$$

In other words, it cannot be the case that $x$ is a nat to nat function and, simultaneously, that the head of the singleton list containing $x$ is a nat.  In other words, $x:\natty \to \natty$ and $\mathsf{head}\,(\mathsf{Cons}(x,\mathsf{Nil})):\natty$ implies false.

Ok, so now I hope you get some intuition about the kinds of possibilities open up with these kind of symmetrical judgements.  But, I guess you may wonder what the type systems, the formal rules, look like.

Here, our key idea is to see type systems as sequent calculi where *the only formulas are typings*.  As is typical for sequent calculi these systems have rules that explain how to justify certain shapes of formula, and the rules can be classified as either left rules or right rules depending on which side of the turnstile the formula appears.  

The right rules include all the "usual" rules that are found in a traditional type system, so all the type systems you already know and love can be thought of as sequent calculi that have only right rules.  The only small difference is that now we can have multiple typings on the right of the turnstile as well as the left, so the judgements are a little more symmetrical, and we use $\Delta$ to stand for a context occurring on the right.  

For example, the right rule for successor explains that one can conclude that $\mathsf{Succ}(M)$ is a nat whenever we can prove that $M$ is a nat.  

$$
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash M : \natty,\,\Delta$}
    \RightLabel{(SuccR)}
    \UnaryInfC{$\Gamma \vdash \mathsf{Succ}(M) : \natty,\,\Delta $}
  \end{prooftree}
$$

The right rule for application explains, as usual, how to affirm that an application $M\,N$ has a type $B$, and to do that we must show that $M$ is an $A$ to $B$ function and $N$ is an appropriately typed argument.

$$
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash M : A \to B,\,\Delta$}
    \AxiomC{$\Gamma \vdash N : A,\,\Delta$}
    \RightLabel{(AppR)}
    \BinaryInfC{$\Gamma \vdash M\,N : B,\,\Delta$}
  \end{prooftree}
$$

More interestingly, we will typically have left rules, which explain how to justify judgements based on a principal formula on the left of the turnstile.  One can think of these rules as explaining how to *refute* a typing of a certain shape but, in practice, they are more often used to extract information from assumptions.  For example, a left rule for the successor function says that, if you want to refute that a term of shape $\mathsf{succ}(M)$ is a nat, then you should refute that $M$ is a nat. 

$$
  \begin{prooftree}
    \AxiomC{$\Gamma,\,M:\natty \vdash \Delta$}
    \RightLabel{(SuccL)}
    \UnaryInfC{$\Gamma,\,\mathsf{Succ}(M):\natty \vdash \Delta$}
  \end{prooftree}
$$

To refute that the ifzero conditional has type $A$, one way is to refute that the then-branch has type $A$ and to refute that the else branch has type $A$, because if neither branch evaluates to an $A$, then the expression cannot possibly evaluate to an $A$.

$$
  \begin{prooftree}
    \AxiomC{$\Gamma,\,P : A \vdash \Delta$}
    \AxiomC{$\Gamma,\,Q : A \vdash \Delta$}
    \RightLabel{(IfzL2)}
    \BinaryInfC{$\Gamma,\,\mathsf{ifz}\,M\,\mathsf{then}\,P\,\mathsf{else}\,Q:A \vdash \Delta$}
  \end{prooftree}
$$

Here's a more interesting left rule, which says how to refute a let-destructor for pairs.  So, suppose we have this let expression on pairs and we want to refute that it evaluates to an $A$.  One way to do that is to say, well, if the let were to evaluate to an $A$, then it must be because the $N$ part evaluates to an $A$ under the appropriate substitution, so we can ask the question what does $N$ require of its free variables $x_1$ and $x_2$ whenever it evaluates to an $A$?  This is the content of the second and third premises below.  Once we have established that "if $N$ is of type $A$ then necessarily each $x_i$ has some type $B_i$ respectively", then we can just refute that $M$ provides components of these types, i.e. refute (here we are on the left of the turnstile) that $M$ is of type $B_1 \times B_2$.

$$
  \begin{prooftree}
    \AxiomC{$\Gamma,\,M : B_1 \times B_2 \vdash \Delta$}
    \noLine
    \UnaryInfC{$\Gamma,\,N:A \vdash x_1 : B_1,\,\Delta$}
    \noLine
    \UnaryInfC{$\Gamma,\,N:A \vdash x_2 : B_2,\,\Delta$}
    \RightLabel{(LetL2)}
    \UnaryInfC{$\Gamma,\,\mathsf{let}\,(x_1,\,x_2) = M\,\mathsf{in}\,N : A \vdash \Delta$}
  \end{prooftree}
$$

Let's look at a very simple example of this in action.  The term $\mathsf{let}\, (x1, x2) = (\lambda x\,.2, 3)\, \mathsf{in}\, (x2,\,x1)$ does not evaluate to a pair whose first component is a $\natty \to \natty$ function and whose second component is a $\natty$.  Why?  Because:

$$
  \begin{prooftree}
    \AxiomC{$(\lambda x.\, 2,\,3) : \natty \times (\natty \to \natty) \vdash $}
    \noLine
    \UnaryInfC{$(x2,\,x1) : (\natty \to \natty) \times \natty \vdash x1 : \natty$}    
    \noLine
    \UnaryInfC{$(x2,\,x1) : (\natty \to \natty) \times \natty \vdash x2 : \natty \to \natty$}   
    \UnaryInfC{$\mathsf{let}\,(x1, x2) = (\lambda x.\,2,\,3)\,\mathsf{in}\,(x2,\,x1) : (\natty \to \natty) \times \natty \vdash$}
  \end{prooftree}
$$

Now, the most interesting part comes when we consider typing lambda calculi, and we want to, for example, refute that an arbitrary application has a given type.  For this, we need another new ingredient: the *necessity function type*.  

$$
A \onlyto B
$$

We pronounce this arrow "$A$ only to $B$".  Intuitively, this is the type of functions that, if they output a $B$, then necessarily their input was an $A$.  To understand it better, let's compare with the usual arrow $A \to B$.

The "usual" function type we will distinguish as the "sufficiency" function type, or sufficiency arrow.  It's introduction rule expresses the notion that a term $M$ depends on a variable $x$ in a certain way, namely if $x$ is of type $A$ then $M$ as a whole will be of type $B$.  

$$
  \begin{prooftree}
    \AxiomC{$\Gamma,\,x:A \vdash M:B,\,\Delta$}
    \RightLabel{(AbsR)}
    \UnaryInfC{$\Gamma \vdash \lambda x.\,M : A \to B,\,\Delta$}
  \end{prooftree}
$$

If we think of functions in terms of providing an output, then this arrow type says that, to obtain an output of type $B$, it is *sufficient* to supply an input of type $A$.

For example, to obtain a nat from the constantly 42 function, it suffices to supply a nat as input.

$$
  \vdash \lambda x.\,42 : \natty \to \natty
$$

To obtain an empty list from the expression `map f`, it suffices to supply an empty list as argument.

$$
  \vdash \mathsf{map}\,f : \nilty \to \nilty
$$

On the other hand, it would not suffice to supply any old list of a if we want to obtain an empty list as output.

$$
  \not\vdash \mathsf{map}\,f : \mathsf{List}(a) \to \nilty
$$

Two-sided systems open up the possibility of expressing another notion of dependency between term and variable, like this:

$$
  \begin{prooftree}
    \AxiomC{$\Gamma,\,M:B \vdash x:A,\,\Delta$}
    \RightLabel{(AbnR)}
    \UnaryInfC{$\Gamma \vdash \lambda x.\,M : A \onlyto B,\,\Delta$}
  \end{prooftree}
$$

Observe how the premise is exactly the mirror of sufficiency.  It says that whenever the output $M$ evaluates to a $B$, necessarily $x$ was an $A$.  

For example, to obtain an $a$ from the head function necessitates that the input was a cons with the value in head being an $a$.  

$$
  \vdash \mathsf{head} : \consty(a,\,\okty) \onlyto a
$$

To obtain an empty list from $\mathsf{map}\,f$, it is necessary we supply an empty list as input.  

$$
  \vdash \mathsf{map}\,f : \nilty \onlyto \nilty
$$

Observe that, with the usual arrow we can express preservation of properties - $\mathsf{map}\,f$ preserves the property of being empty, but with the necessity arrow we can express reflection of properties - $\mathsf{map}\,f$ reflects the property of being empty.

Finally, it is *not* necessary that the constantly 42 function requires a nat to return a nat.

$$
  \not\vdash \lambda x.42 : \natty \onlyto \natty
$$

With necessity, we can explain how to refute that a term of shape $M\,N$ -- i.e. an arbitrary application of a function to an argument -- has some type $B$.  
If I want to refute that $M\,N$ has type $B$, then one approach is to *affirm* that $M$ is a function that, in order to produce a $B$, *necessarily* requires an A, and then *refute* that it's actual parameter $N$ is an $A$.  If you think about it, sufficiency is not enough to carry out this deduction.

$$
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash M : A \onlyto B,\,\Delta$}
    \AxiomC{$\Gamma,\,N:A \vdash \Delta$}
    \RightLabel{(AppL)}
    \BinaryInfC{$\Gamma,\,M\,N : B \vdash \Delta$}
  \end{prooftree}
$$

For example, the identity applied to 2 is not a function:

$$
\begin{prooftree}
  \AxiomC{$\lambda x.x : (\natty \to \natty) \onlyto (\natty \to \natty)$}
  \AxiomC{$2 : \natty \to \natty \vdash$}
  \BinaryInfC{$(\lambda x.x)\,2 : \natty \to \natty \vdash$}
\end{prooftree}
$$

As I said earlier, more usually we use left rules not to refute a formula outright, but rather to extract useful information about the subterms.   Here is a complete derivation of the fact that $(\lambda x.x)\,y$ being a nat implies that $y$ must be a nat:

$$
\begin{prooftree}
  \AxiomC{}
  \UnaryInfC{$x:\natty \vdash x:\natty$}
  \UnaryInfC{$\vdash \lambda x.x : \natty \onlyto \natty$}
  \AxiomC{}
  \UnaryInfC{$y:\natty \vdash y:\natty$}
  \BinaryInfC{$(\lambda x.x)\,y : \natty \vdash y:\natty$}
\end{prooftree}
$$

Ok, now you've seen an extremely brief glimpse at what typing really looks like, you may wonder what it is good for, so let's return to incorrectness.

If we introduce a type of all values, we call it $\okty$, that acts as the top of the subtyping order, then we can express not only that some term evaluates to a nat, or evaluates to an a, but that a given term evaluates full-stop - that a term reaches a value.

Then, by concluding on the left hand side, we can refute that a term reaches a value.  For example, we can refute that head of the empty list reaches a value.  It follows using the application on the left rule, because (as we saw earlier) for head to return a value, *necessarily* it is given a cons, but we can easily refute that the empty list is a cons.

$$
\begin{prooftree}
  \AxiomC{$\vdash \mathsf{head} : \consty(\natty,\,\okty) \onlyto \natty$}
  \AxiomC{$[] : \consty(\natty, \okty) \vdash$}
  \BinaryInfC{$\mathsf{head}\,[] : \natty \vdash$}
\end{prooftree}
$$

Thus in two-sided systems soundness amounts to two things.  First, *well-typed programs don't go wrong* and, since $\okty$ is the top of the type hierarchy we can formulate *well-typed* for closed terms $M$ just as proving that $M$ has type $\okty$ on the right.

$$
  \vdash M : \okty
$$

Then, symmetrically, if a closed term has type $\okty$ on the *left*, so we refute that it reaches a value, then we say that it is *ill-typed* and we obtain the theorem that *ill-typed programs don't evaluate*: every ill-typed program either crashes or diverges.

$$
  M : \okty \vdash
$$

Of course there are still programs that are untypable.  For example, $\lambda x. (x\,3,\,x\,(\lambda y.y))$ is untypable - intuitively, two-sided systems do not give us any additional power on the right of the turnstile, i.e. to prove that programs are well-typed.  This program will not go wrong, but we need higher-rank polymorphism to express its type.  We could of course have a two-sided system with higher-rank types, but it is orthogonal from the two-sidedness.

In the paper, in addition to introducing the basic ideas, we have three major contributions.  

* The first is in working out the CBV semantics of a 2-sided system for PCF, analysing the expressive power of the new necessity arrow and proving a semantic soundness result.
* The second is in analysing the relationship with type complement, introducing a non-standard "success" semantics and showing that this alternative semantics allows for a compression of the two-sided system entirely onto the right hand side.
* The third is in developing a constrained 2-sided type system for pattern matching safety, and showing two-sided versions of progress and preservation, and working out fully-automatic type inference in the style of constraint generation and resolution.

<!-- 
  * Since the ability to put typing formulas on the left gives a way to refute, a natural question is the relationship with negation in type systems, such as a complement type operator.  This actually turns out to be a little subtle, because of the presence of effects like non-termination and crashing.  We introduce a complement operator on types - since our language is CBV, types are just sets of values so the semantics of the complement operator is to complement the set of values wrt to the universe of all values.  Then we phrase this question as whether or not judgements of shape M:A |- can be internalised into the type A^c, i.e. whether M:A |- iff |- M:A^c.  Under the standard CBV semantics, this equivalence does not hold, effectively because M:A on the left allows M to crash, but M:A^c on the right does not.  However, by changing the semantics to allow for terms to crash on the right, we can obtain this equivalence.  This alternative semantics has the same flavour of the semantics of Erlang success types, and so we call it the success semantics and it validates the "standard" rules (CompL) and (CompR) which yield this equivalence.  The success semantics is unusual, it supports a true positives theorem: ill-typed program don't evaluate, but it doesn't support a true positives theorem: well-typed programs don't go wrong.  But it's actually a very nice semantics and is, in some sense more symmetrical than the standard CBV semantics.  For example, in the success semantics we can actually define >- in terms of ->, A >- B := A^c -> B^c.  In other words, the necessity arrow is really the contrapositive of the usual sufficiency arrow - a function f has type A only to B just if when you give f a value outside of A, then it guarantees to give you back a value outside of B.  Rather surprisingly, because all our typing rules have a particular property, we can use (CompL) and (CompR) to derive (in the sense of derivable rule) a traditional one-sided system, using only the sufficiency arrow ->, in the success semantics that is actually more expressive than our two-sided system in the success semantics. -->
