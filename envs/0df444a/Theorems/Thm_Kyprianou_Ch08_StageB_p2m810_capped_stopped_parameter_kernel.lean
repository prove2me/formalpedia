-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_capped_stopped_parameter_kernel
-- name    : Kyprianou.Ch08.StageB.p2m810_capped_stopped_parameter_kernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:03:13.067907+00:00
-- url     : https://prove2.me/theorems/50b5a8d3-0d6e-47b3-a938-c8833794b2d7
-- title:
--   Use the capped finite clock and stopped parameter, apply the joint path product law on the stopped cap event, and integrate the bounded reward.
-- statement:
--   Use the capped finite clock and stopped parameter, apply the joint path product law on the stopped cap event, and integrate the bounded reward.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_capped_stopped_parameter_kernel
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (H : (ℝ≥0 × ℝ) × (ℝ≥0 → ℝ) → ℝ) (hH : Measurable H)
    (hb : ∀ z, 0 ≤ H z ∧ H z ≤ 1) (n : ℝ≥0) :
    let ρ := fun ω => WithTop.untopD 0 (min (τ ω) (n : WithTop ℝ≥0))
    let p := fun ω => if τ ω ≤ (n : WithTop ℝ≥0) then
      H ((ρ ω,X.X (ρ ω) ω),fun s => X.X (ρ ω+s) ω - X.X (ρ ω) ω) else 0
    let r := fun ω => if τ ω ≤ (n : WithTop ℝ≥0) then
      (∫ η, H ((ρ ω,X.X (ρ ω) ω),fun s => X.X s η) ∂P) else 0
    Measurable p ∧ Measurable r ∧ (∫ ω, p ω ∂P) = ∫ ω, r ω ∂P := by
  sorry
