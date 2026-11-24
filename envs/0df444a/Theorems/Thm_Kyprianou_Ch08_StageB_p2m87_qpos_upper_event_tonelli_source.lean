-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_upper_event_tonelli_source
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_upper_event_tonelli_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:58:39.503602+00:00
-- url     : https://prove2.me/theorems/b5091ab3-4654-47e6-bba2-d6225d139d61
-- title:
--   Tonelli and source transfer for upper-passage occupation
-- statement:
--   Apply Tonelli to the jointly measurable upper-passage occupation event, and use almost-sure equality of clocks and paths to transfer to the source model.
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

theorem Kyprianou.Ch08.StageB.p2m87_qpos_upper_event_tonelli_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    (∫⁻ ω, ∫⁻ t : ℝ≥0, disc t *
      (if U ω ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A
        then 1 else 0) ∂positiveTimeLebesgue ∂P) =
      ∫⁻ t : ℝ≥0, disc t *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue
:= by
  sorry
