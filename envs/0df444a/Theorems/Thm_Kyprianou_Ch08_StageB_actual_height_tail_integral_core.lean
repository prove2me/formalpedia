-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_integral_core
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_integral_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:48:48.907442+00:00
-- url     : https://prove2.me/theorems/fa1082de-2ae4-4875-87d7-ea88445d4e80
-- title:
--   Theorem 8.2 actual-height integral core: positivity, monotonicity, continuity and unit limit
-- statement:
--   Under the exact hypotheses of Theorem 8.2, the actual-height integral E(h) over the no-drawdown event with the discounted payoff is positive on positive heights, monotone there, right-continuous, tends to 1 at infinity, and is left-continuous. This is the hard stochastic-analysis core; the parent tail-regularity theorem follows by elementary -log glue.
-- source:
--   Source-faithful decomposition child of Kyprianou Chapter 8 Theorem 8.2 actual-height tail regularity (parent cb2a2350-eb86-4275-a402-31ab4d6297f3): isolates the integral-core package (positivity, monotonicity, right-continuity, unit limit, left-continuity) with the exact original-path event and payoff from Definitions.Def_Kyprianou_Ch08_StageCFoundation_D. Parent bridge: F(h) = -Real.log (E(h)) via Real.log monotonicity/continuity and neg glue.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_integral_core
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    (∀ h : ℝ, 0 < h → 0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) ∧
    MonotoneOn (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ioi 0) ∧
    (∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ici h₀) h₀) ∧
    Tendsto (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) atTop (nhds 1) ∧
    (∀ y : ℝ, 0 < y → Tendsto (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (nhdsWithin y (Set.Iio y)) (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) := by
  sorry
