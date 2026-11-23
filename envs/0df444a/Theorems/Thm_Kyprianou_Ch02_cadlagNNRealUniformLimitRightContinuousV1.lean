-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagNNRealUniformLimitRightContinuousV1
-- name    : Kyprianou.Ch02.cadlagNNRealUniformLimitRightContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:07:00.34952+00:00
-- url     : https://prove2.me/theorems/d56b13e9-b9de-4916-8791-579c34f69e61
-- title:
--   Uniform limit of càdlàg functions is right-continuous
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
theorem cadlagNNRealUniformLimitRightContinuousV1
    (f : ℝ≥0 → ℝ)
    (happrox : ∀ T : ℝ≥0, 0 < T →
      ∃ (F : ℕ → ℝ≥0 → ℝ),
        (∀ n, ProbabilityTheory.IsCadlag (F n)) ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T →
            |F n t - f t| < δ) :
    ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t
    := by sorry
end Kyprianou.Ch02
