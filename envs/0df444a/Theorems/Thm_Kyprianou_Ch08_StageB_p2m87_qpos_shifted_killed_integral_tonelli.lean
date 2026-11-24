-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_shifted_killed_integral_tonelli
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_shifted_killed_integral_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:57:22.172959+00:00
-- url     : https://prove2.me/theorems/ab9ff19c-ee9a-4b67-92cb-4db2703a4d96
-- title:
--   8.7 shifted killed occupation integral via Tonelli
-- statement:
--   Integrate the discounted killed reward evaluated after the finite upper exit; translation in time and Tonelli identify this integral with the time integral of the upper-passage and lower-survival event. This is the measure-theoretic component of the stopped-payoff occupation identity.
-- source:
--   Kyprianou (2006), Theorem 8.7; exact reduction of ee0147bb-3081-4409-86c6-bbfddc4c9b01, separating the pathwise post-stopping reward from the time integral.

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

theorem Kyprianou.Ch08.StageB.p2m87_qpos_shifted_killed_integral_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    let R : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
      if U ω < L ω then disc t *
        (if (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A then 1 else 0) else 0
    (∫⁻ ω, ∫⁻ s : ℝ≥0, R (τ ω + s) ω ∂positiveTimeLebesgue ∂P) =
      ∫⁻ t : ℝ≥0, disc t *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue
:= by
  sorry
