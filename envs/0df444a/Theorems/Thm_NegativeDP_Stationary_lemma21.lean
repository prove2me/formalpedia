-- Prove2me | Theorems.Thm_NegativeDP_Stationary_lemma21
-- name    : NegativeDP.Stationary.lemma21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:29.968446+00:00
-- url     : https://prove2.me/theorems/e290cb86-6797-44ae-91c3-da3bc7de76b0
-- title:
--   Lemma 2.1 (N) — a degenerate kernel f with fu ≥ qu
-- statement:
--   Let $X$ and $Y$ be non-empty Borel sets, let $q(\cdot\mid x)$ be a probability kernel from $X$ to $Y$, and let $u\in M(XY)$, that is, $u:X\times Y\to[-\infty,0]$ is Borel. Write $qu(x)=\int u(x,y)\,dq(y\mid x)$. Then there is a Borel map $f:X\to Y$ such that
--
--   $$u(x,f(x))\;\ge\;qu(x)\qquad\text{for every }x\in X.$$
--
--   In the paper's words, $f$ is a degenerate element of $Q(Y\mid X)$ with $fu\ge qu$: a randomized choice of $y$ given $x$ can be replaced by a non-random measurable one whose return is at least as large at every $x$. This selection lemma is what turns randomized policies into non-random ones in Theorem 4.3.
--
--   **Formalization Note.** The paper states the lemma for the class $M(XY)$ of each of its three cases; this item is the negative case (non-positive, extended-real valued $u$). Borel sets are non-empty standard Borel types and $qu$ is computed as $-\int(-u)\,dq$ in $[0,\infty]$, so that $qu(x)=-\infty$ is allowed.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 874, Lemma 2.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

/-- Lemma 2.1 (p. 874), negative case: for a probability kernel `q ∈ Q(Y | X)` and
`u ∈ M(XY)` there is a measurable `f : X → Y` with `fu ≥ qu`, i.e.
`u(x, f(x)) ≥ ∫ u(x, y) dq(y | x)` for every `x`. -/
theorem lemma21 {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (q : Kernel X Y) [IsMarkovKernel q] (u : X × Y → EReal) (hu : IsNegM u) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, kint q u x ≤ u (x, f x) := by sorry

end NegativeDP.Stationary
