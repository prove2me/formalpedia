-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagNNRealUniformLimitLeftLimitsV1
-- name    : Kyprianou.Ch02.cadlagNNRealUniformLimitLeftLimitsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:06:58.191248+00:00
-- url     : https://prove2.me/theorems/00f5291a-bf9e-40db-9c1d-f09101819ea1
-- title:
--   Uniform limit of càdlàg functions has left limits
-- statement:
--   Deterministic regularity component of the local uniform càdlàg closure theorem on ℝ≥0, for horizon-dependent approximating sequences, with the exact original hypotheses.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.4 and Theorem 2.10

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Filter Set Topology ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem cadlagNNRealUniformLimitLeftLimitsV1
    (f : ℝ≥0 → ℝ)
    (happrox : ∀ T : ℝ≥0, 0 < T →
      ∃ (F : ℕ → ℝ≥0 → ℝ),
        (∀ n, ProbabilityTheory.IsCadlag (F n)) ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T →
            |F n t - f t| < δ) :
    ∀ t : ℝ≥0, ∃ l : ℝ,
      Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)
    := by sorry
end Kyprianou.Ch02
