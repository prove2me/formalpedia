-- Prove2me | Theorems.Thm_Function_orbitCensus_of_dihedralThree_relations
-- name    : Function.orbitCensus_of_dihedralThree_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/152f449d-e5f2-57d2-a708-8be500ae5d90
-- title:
--   Orbit census for a dihedral pair of order-two and order-three maps
-- statement:
--   Let $X$ be a finite type with decidable equality and let $a, b : X \to X$ be maps satisfying the relations $a(a(x)) = x$, $b(b(b(x))) = x$ and $a(b(x)) = b(b(a(x)))$ for all $x$, so that $a$ and $b$ generate an action on $X$ of a quotient of $S_3 = \langle a,b \mid a^2, b^3, abab\rangle$. Let $\iota$ be a type with decidable equality and $c : X \to \iota$ a map whose fibres are exactly the orbits, in the precise sense that $c(x) = c(y)$ holds if and only if $y$ is one of $x$, $a(x)$, $b(x)$, $b(b(x))$, $a(b(x))$, $a(b(b(x)))$; and let $S$ be a finite subset of $\iota$ whose members are exactly the values taken by $c$. Writing $n_p$ for the cardinality of the fibre $c^{-1}(p)$, the conclusion is the conjunction of three assertions: $n_{c(x)} \in \{1,2,3,6\}$ for every $x \in X$; the number of $p \in S$ with $n_p = 1$ or $n_p = 3$ equals the number of $x \in X$ with $a(x) = x$; and the number of $p \in S$ with $n_p = 1$, plus twice the number with $n_p = 2$, equals the number of $x \in X$ with $b(x) = x$.
--
--   This is the counting content of the rows of $\langle a \rangle \cong C_2$ and $\langle b \rangle \cong C_3$ in the table of marks of $S_3$: on a transitive $S_3$-set of size $1,2,3,6$ an involution has $1,0,1,0$ fixed points and an element of order three has $1,2,0,0$, and summing over orbits gives the two identities. It is phrased for a pair of maps rather than for a group action so as to apply directly to operators on a finite set obeying the same relations, and is used in the computation of orders and censuses attached to modular curves in characteristic three ([`ModularCurve.ord_census_qExpFunctionFieldC_gammaH_of_char_three`](thm.html#ModularCurve.ord_census_qExpFunctionFieldC_gammaH_of_char_three) and [`ModularCurve.ord_jqModC_census_of_char_three`](thm.html#ModularCurve.ord_jqModC_census_of_char_three)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Function_orbitCensus_of_dihedralThree_relations.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Function.orbitCensus_of_dihedralThree_relations
    {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))
    {ι : Type*} [DecidableEq ι] (c : X → ι)
    (hc : ∀ x y, c x = c y ↔
      (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))
    (S : Finset ι) (hS : ∀ p, p ∈ S ↔ ∃ x, c x = p) :
    (∀ x, (Finset.univ.filter fun y => c y = c x).card = 1 ∨
        (Finset.univ.filter fun y => c y = c x).card = 2 ∨
        (Finset.univ.filter fun y => c y = c x).card = 3 ∨
        (Finset.univ.filter fun y => c y = c x).card = 6) ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 ∨
        (Finset.univ.filter fun y => c y = p).card = 3).card =
      (Finset.univ.filter fun x => a x = x).card ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1).card +
        2 * (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2).card =
      (Finset.univ.filter fun x => b x = x).card := by sorry
