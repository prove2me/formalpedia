-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_integral_core_left_continuous
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_integral_core_left_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:58:00.330859+00:00
-- url     : https://prove2.me/theorems/2009363d-eef9-4af6-8fe2-05d306fd4366
-- title:
--   Theorem 8.2 actual-height integral core with left continuity
-- statement:
--   Corrected version of Kyprianou Chapter 8 Theorem 8.2 integral core. It keeps the exact original imports, parameters, event, discounted payoff, and all five conjuncts, but replaces right continuity within Set.Ici h₀ by left continuity within Set.Iic h₀. The source closed-tail identity makes right continuity fail at atoms of the canonical height measure, which source Lemma 8.2 explicitly permits.
-- source:
--   Source-faithful correction of target fa1082de-2ae4-4875-87d7-ea88445d4e80 using sourceCertificate_result8_2 from Definitions.Def_Kyprianou_Ch08_StageCFoundation_D; corrects the right-continuity branch identified in the retirement note.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_integral_core_left_continuous
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    (∀ h : ℝ, 0 < h → 0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) ∧
    MonotoneOn (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ioi 0) ∧
    (∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Iic h₀) h₀) ∧
    Tendsto (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) atTop (nhds 1) ∧
    (∀ y : ℝ, 0 < y → Tendsto (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (nhdsWithin y (Set.Iio y)) (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) := by
  sorry
