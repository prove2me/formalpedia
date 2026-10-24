-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_8
-- name    : OnlineMaxWeightMatch.Approx.proposition_2_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:48.124104+00:00
-- url     : https://prove2.me/theorems/6f200e16-9506-4db2-a09e-e97bdf5b5dae
-- title:
--   Proposition 2.8: negatively associated variables are pairwise non-positively correlated
-- statement:
--   Let $X_1,\dots,X_n$ be negatively associated random variables on a probability space. Then for all $i\neq j$,
--
--   $$
--   \operatorname{Cov}(X_i,X_j)\le 0.
--   $$
--
--   It follows from (1) with $f(\vec X)=X_i$ and $g(\vec X)=X_j$, and it is the form in which the paper uses negative association (Corollary 4.10).
--
--   **Formalization Note** $X_i$ and $X_j$ are assumed square-integrable, so that the covariance is the usual one; Lean's `covariance` would otherwise take a junk value.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 5, Proposition 2.8

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Proposition 2.8. Negatively associated random variables are pairwise non-positively
correlated: `Cov(X_i, X_j) ≤ 0` for `i ≠ j` (for square-integrable `X_i`, `X_j`). -/
theorem proposition_2_8 {Ω κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : κ → Ω → ℝ) (hNA : NegativelyAssociated X μ)
    {i j : κ} (hij : i ≠ j) (hi : MemLp (X i) 2 μ) (hj : MemLp (X j) 2 μ) :
    cov[X i, X j; μ] ≤ 0 := by sorry

end OnlineMaxWeightMatch.Approx
