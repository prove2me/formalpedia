-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableLevyExtendedMomentMulV1
-- name    : Kyprianou.Ch03.stableLevyExtendedMomentMulV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:01:55.443517+00:00
-- url     : https://prove2.me/theorems/930d8261-1d54-4715-b17f-8adae94fa738
-- title:
--   Multiplicativity of extended Lévy exponential moments
-- statement:
--   Use independent stationary increments and Tonelli.
-- source:
--   Kyprianou (2006), Exercise 3.7; extracted from accepted proof of source_result81_finite_moment_log_scaling.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableLevyExtendedMomentMulV1 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (θ : ℝ) (s u : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (s + u) ω)) ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X u ω)) ∂P := by sorry
