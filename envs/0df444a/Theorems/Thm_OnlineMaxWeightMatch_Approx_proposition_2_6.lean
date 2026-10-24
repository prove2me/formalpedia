-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_6
-- name    : OnlineMaxWeightMatch.Approx.proposition_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:51.280392+00:00
-- url     : https://prove2.me/theorems/e0a60fd8-310c-4920-b9a4-ad09c69cd2b8
-- title:
--   Proposition 2.6 (0-1 Principle): binary variables summing to at most one are negatively associated
-- statement:
--   Let $X_1,\dots,X_n$ be random variables on a probability space, each taking values in $\{0,1\}$, such that
--
--   $$
--   \sum_i X_i\le 1\quad\text{always}.
--   $$
--
--   Then the family $(X_1,\dots,X_n)$ is negatively associated.
--
--   This is the basic source of negative association in the paper: for a fixed ball $t$, the indicators "ball $t$ arrives and picks bin $i$ first" sum to at most one, so they are NA, which starts the proof of Lemma 4.9.
--
--   **Formalization Note** The variables are indexed by a finite type and assumed measurable; "always" is read pointwise on $\Omega$.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 5, Proposition 2.6

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Proposition 2.6 (0-1 Principle). Binary random variables whose sum is at most `1` always are
negatively associated. -/
theorem proposition_2_6 {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : κ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hbin : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hsum : ∀ ω, ∑ i, X i ω ≤ 1) :
    NegativelyAssociated X μ := by sorry

end OnlineMaxWeightMatch.Approx
