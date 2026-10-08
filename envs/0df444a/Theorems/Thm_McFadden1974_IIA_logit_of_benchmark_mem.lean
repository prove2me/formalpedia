-- Prove2me | Theorems.Thm_McFadden1974_IIA_logit_of_benchmark_mem
-- name    : McFadden1974.IIA.logit_of_benchmark_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:11.627979+00:00
-- url     : https://prove2.me/theorems/7a40d4c3-5c00-4732-aa89-aa16f5ce086b
-- title:
--   Equation (10) — logit form with a benchmark member $z$ of the alternative set
-- statement:
--   Assume the standing conditions and Axioms 1 and 2. For an attribute vector $s$, a possible alternative set $B$ and a benchmark $z\in B$, define $V(s,x,z) = \log(p_{xz}/p_{zx})$, where $p_{xy} = P(x\mid s,\{x,y\})$ for $x\neq y$ and $p_{xx}=\tfrac12$. Then for every $x\in B$,
--   $$P(x\mid s,B) = \frac{e^{V(s,x,z)}}{\sum_{y\in B} e^{V(s,y,z)}}.$$
--
--   This is the logit form with a function $V$ that may depend on the benchmark, and so on the alternative set; the paper interprets $s$, $x$ and $z$ as a measured taste effect, a choice alternative effect and an alternative set effect.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 110, Equation (10) (PDF p. 6)

import Mathlib
import Definitions.Def_McFadden1974_IIA_ChoiceModel

namespace McFadden1974.IIA

/-- **Equation (10)** (p. 110, PDF p. 6): "Taking z to be a 'benchmark' member of the alternative
set B and defining V(s, x, z) = log(p_xz/p_zx), Equation (8) can be written
(10) P(x | s, B) = e^{V(s,x,z)} / Σ_{y∈B} e^{V(s,y,z)}."

Formalization Note: standing assumptions `IsSelectionProb` and `PairsPossible`, and Axioms 1
and 2; the benchmark `z` is a member of `B`. `altSetV P s x z` is `V(s, x, z)`, which depends
on the benchmark `z` and hence, through the choice `z ∈ B`, on the alternative set. -/
theorem logit_of_benchmark_mem {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (z : X) (hz : z ∈ B) (x : X) (hx : x ∈ B) :
    P s B x = Real.exp (altSetV P s x z) / ∑ y ∈ B, Real.exp (altSetV P s y z) := by sorry

end McFadden1974.IIA
