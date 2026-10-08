-- Prove2me | Theorems.Thm_McFadden1974_IIA_logit_of_universal_benchmark
-- name    : McFadden1974.IIA.logit_of_universal_benchmark
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:57.454624+00:00
-- url     : https://prove2.me/theorems/bfac1dfd-5dfd-4468-b81b-f84b8507888b
-- title:
--   Footnote 3 — Axioms 1–2 and a universal benchmark yield the logit form (12)
-- statement:
--   Assume that each $P(\cdot\mid s,B)$ is a probability vector on every possible alternative set $B$, that two-element subsets of possible sets are possible, and that Axioms 1 (Independence of Irrelevant Alternatives) and 2 (Positivity) hold. Suppose $z$ is a **universal benchmark**: whenever $B$ is a possible alternative set, so is $B\cup\{z\}$. Define
--   $$v(s,x) = V(s,x,z) = \log\frac{p_{xz}}{p_{zx}},\qquad p_{xy} = P(x\mid s,\{x,y\})\ (x\neq y),\quad p_{xx}=\tfrac12.$$
--   Then for every attribute vector $s$, every possible alternative set $B$ (whether or not it contains $z$) and every $x\in B$,
--   $$P(x\mid s,B) = \frac{e^{v(s,x)}}{\sum_{y\in B} e^{v(s,y)}}.$$
--
--   Thus Axiom 3 (Irrelevance of Alternative Set Effect) follows from Axioms 1 and 2, and the selection probabilities take the conditional logit form (12) with a single "utility indicator" $v$ shared by all alternative sets.
--
--   **Formalization Note** The conclusion uses the paper's explicit $v$, which is stronger than asserting that some $v$ exists; $v$ does not depend on $B$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 110, footnote 3 and Equation (12) (PDF p. 6)

import Mathlib
import Definitions.Def_McFadden1974_IIA_ChoiceModel

namespace McFadden1974.IIA

/-- **Footnote 3 with Equation (12)** (p. 110, PDF p. 6): "Axiom 3 follows from Axioms 1 and 2 if
there exists some 'universal benchmark' alternative z such that if B is a possible alternative
set, then B ∪ {z} is also. This follows by noting that Equation (9) holds for z ∉ B, provided
Axioms 1 and 2 holds for B ∪ {z}. Then, taking z to be the universal benchmark in Equation (10)
and defining v(s, x) = V(s, x, z) for all alternative sets yields the result." The result is
(12): "P(x | s, B) = e^{v(s,x)} / Σ_{y∈B} e^{v(s,y)}."

Formalization Note: standing assumptions `IsSelectionProb` (each `P(· | s, B)` is a probability
vector on a possible `B`) and `PairsPossible` (two-element subsets of possible sets are
possible), Axioms 1 and 2 on the possible sets, and a universal benchmark `z`. The conclusion
is (12) with the paper's explicit `v(s, x) = V(s, x, z) = log(p_xz/p_zx)`, one function of
`(s, x)` for **all** possible alternative sets, including those not containing `z`; this is
stronger than `∃ v` and is never the set-dependent form (10). -/
theorem logit_of_universal_benchmark {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (z : X) (hz : IsUniversalBenchmark poss z) :
    ∀ s : S, ∀ B ∈ poss, ∀ x ∈ B,
      P s B x = Real.exp (altSetV P s x z) / ∑ y ∈ B, Real.exp (altSetV P s y z) := by sorry

end McFadden1974.IIA
