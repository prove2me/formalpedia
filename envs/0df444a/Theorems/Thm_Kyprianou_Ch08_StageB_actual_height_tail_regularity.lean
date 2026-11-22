-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_regularity
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_regularity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T19:04:47.055079+00:00
-- url     : https://prove2.me/theorems/cb2a2350-eb86-4275-a402-31ab4d6297f3
-- title:
--   Theorem 8.2 actual-height tail regularity: antitone, right-continuous, vanishing with left-limit link
-- statement:
--   Under the exact hypotheses of Theorem 8.2, the actual tail F(h) = -log S(1,h) is antitone on positive heights, right-continuous, vanishes at infinity, and satisfies the left-limit link identifying -F as the left limit of -G. These are the Stieltjes regularity hypotheses needed to build the excursion-height measure from the process law.
-- source:
--   Source-faithful decomposition child of Kyprianou Chapter 8 Theorem 8.2 actual-height law (parent 3eded364-8075-43f9-bae4-12db613bec33): isolates the tail-function regularity package (gaps hGanti/hGcont/hGtop/hlink) with the exact original-path event and payoff from Definitions.Def_Kyprianou_Ch08_StageCFoundation_D.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_regularity
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    AntitoneOn (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ioi 0) ∧
    (∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ici h₀) h₀) ∧
    Tendsto (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) atTop (nhds 0) ∧
    (∀ y : ℝ, 0 < y → Tendsto (fun s => -(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 s ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) (nhdsWithin y (Set.Iio y)) (nhds (-(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))))) := by
  sorry
