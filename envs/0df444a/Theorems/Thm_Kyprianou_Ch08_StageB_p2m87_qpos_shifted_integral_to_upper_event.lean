-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_shifted_integral_to_upper_event
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_shifted_integral_to_upper_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:58:35.859821+00:00
-- url     : https://prove2.me/theorems/d50bed04-e578-4ede-8835-6dc68c4e3367
-- title:
--   Translate stopped killed integral to upper-passage event
-- statement:
--   Apply the proved nonnegative-time translation to the stopped integrand, and identify the indicator of upper passage by time t and survival beyond t.
-- source:
--   Kyprianou (2006), Theorem 8.7; reduction of ab9ff19c-ee9a-4b67-92cb-4db2703a4d96.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem Kyprianou.Ch08.StageB.p2m87_qpos_shifted_integral_to_upper_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q a x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    let R : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
      if U ω < L ω then disc t *
        (if (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A then 1 else 0) else 0
    (∫⁻ ω, ∫⁻ s : ℝ≥0, R (τ ω + s) ω ∂positiveTimeLebesgue ∂P) =
    (∫⁻ ω, ∫⁻ t : ℝ≥0, disc t *
      (if U ω ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A
        then 1 else 0) ∂positiveTimeLebesgue ∂P)
:= by
  sorry
