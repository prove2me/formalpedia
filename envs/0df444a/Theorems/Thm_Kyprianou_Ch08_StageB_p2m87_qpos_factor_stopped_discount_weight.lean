-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_stopped_discount_weight
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_stopped_discount_weight
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T04:25:47.57818+00:00
-- url     : https://prove2.me/theorems/abdee683-5b98-42ad-8ddb-21d1eb2a5501
-- title:
--   Stopped discount mass is the source up-before-down payoff
-- statement:
--   The discounted upper-before-lower stopped mass in the filtered Avram model is the extended-nonnegative lift of the source up-before-down expectation.

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

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_stopped_discount_weight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (hq : 0 < q) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    (∫⁻ ω, if U ω < L ω then disc ((U ω).toNNReal) else 0 ∂P) =
      ENNReal.ofReal (upBeforeDownExpectation P D.X q x a)
:= by
  sorry
