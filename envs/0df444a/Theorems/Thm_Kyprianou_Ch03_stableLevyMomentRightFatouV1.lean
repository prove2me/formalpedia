-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableLevyMomentRightFatouV1
-- name    : Kyprianou.Ch03.stableLevyMomentRightFatouV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:01:52.676215+00:00
-- url     : https://prove2.me/theorems/10b2d121-0df7-4afd-a9fe-3862bc468624
-- title:
--   Right Fatou inequality for Lévy exponential moments
-- statement:
--   Use right-continuous paths and Fatou.
-- source:
--   Kyprianou (2006), Exercise 3.7; extracted from accepted proof of source_result81_finite_moment_log_scaling.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableLevyMomentRightFatouV1 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (θ : ℝ) (s : ℝ≥0) (sn : ℕ → ℝ≥0)
    (hge : ∀ n, s ≤ sn n) (ht : Tendsto sn atTop (nhds s)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (sn n) ω)) ∂P) atTop := by sorry
