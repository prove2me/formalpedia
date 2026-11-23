-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagNNRealOfLocalUniformLimitsV1
-- name    : Kyprianou.Ch02.cadlagNNRealOfLocalUniformLimitsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:03:03.695438+00:00
-- url     : https://prove2.me/theorems/1a902f1e-8367-419b-912c-b59a0f149ea8
-- title:
--   Càdlàg closure under horizon-dependent compact-uniform approximation
-- statement:
--   A real-valued càdlàg path on the nonnegative time axis is preserved under deterministic uniform convergence on each finite horizon, even when the approximating sequence may depend on the horizon. For each time t choose the horizon t+1, transfer right continuity by the triangle inequality, and take the Cauchy limit of left limits using the nontrivial left neighbourhood when t>0. At t=0 the left filter is bottom. This is the deterministic core of the Theorem 2.10 uniform-convergence path argument.
-- source:
--   Kyprianou (2006), Exercise 2.4 and Theorem 2.10; LeanLevy Processes.Cadlag uniform closure

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Filter Set Topology ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem cadlagNNRealOfLocalUniformLimitsV1
    (f : ℝ≥0 → ℝ)
    (happrox : ∀ T : ℝ≥0, 0 < T →
      ∃ (F : ℕ → ℝ≥0 → ℝ),
        (∀ n, ProbabilityTheory.IsCadlag (F n)) ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : ℝ≥0, t ≤ T →
            |F n t - f t| < δ) :
    ProbabilityTheory.IsCadlag f
    := by sorry
end Kyprianou.Ch02
