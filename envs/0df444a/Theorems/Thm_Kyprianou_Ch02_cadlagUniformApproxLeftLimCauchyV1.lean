-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagUniformApproxLeftLimCauchyV1
-- name    : Kyprianou.Ch02.cadlagUniformApproxLeftLimCauchyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:09:44.081107+00:00
-- url     : https://prove2.me/theorems/cbf48642-184f-4396-ab52-f766be4f1bb4
-- title:
--   Cauchy sequence of left limits under compact-uniform convergence
-- statement:
--   An approximating family with finite left limits and uniform convergence on the horizon t+1 has a Cauchy sequence of left-limit values at each positive t. This isolates the essential completeness step of Chapter 2 uniform càdlàg closure.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.4 and Theorem 2.10

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Filter Set Topology ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem cadlagUniformApproxLeftLimCauchyV1
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (F : ℕ → ℝ≥0 → ℝ) (l : ℕ → ℝ)
    (hl : ∀ n, Tendsto (F n) (𝓝[<] t) (𝓝 (l n)))
    (huni : ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ s : ℝ≥0, s ≤ t + 1 →
        |F n s - f s| < δ) :
    CauchySeq l
    := by sorry
end Kyprianou.Ch02
