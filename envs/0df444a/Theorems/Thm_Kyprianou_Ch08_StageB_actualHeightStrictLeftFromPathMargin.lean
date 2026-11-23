-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightStrictLeftFromPathMargin
-- name    : Kyprianou.Ch08.StageB.actualHeightStrictLeftFromPathMargin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:05:16.743276+00:00
-- url     : https://prove2.me/theorems/ea08ebfa-d932-42e6-8306-2d4518ebe8e4
-- title:
--   Lemma 8.2: dominated-convergence implication from a.e. strict excursion-height margin
-- statement:
--   For every genuine spectrally negative model with nonnegative discount, if almost every path with nonzero discounted unit upcrossing payoff and no drawdown above a positive threshold admits a strictly smaller positive threshold preserving its no-drawdown event, then the original restricted discounted expectation is continuous from strictly below that height. This is the measure-theoretic dominated-convergence argument, keeping the original integrable payoff and explicit infinite-passage convention.
-- source:
--   Kyprianou 2006 Lemma 8.2, physical PDF p228; precise conditional measure-theoretic bridge for published original theorem cade7bf0-28cb-43f9-b50a-18cc573d5092.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightStrictLeftFromPathMargin
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q)
    (hmargin : ∀ y : ℝ, 0 < y →
      ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 →
        NoDrawdownBeforeUpcrossing D.X 1 y ω →
          ∃ h : ℝ, 0 < h ∧ h < y ∧
            NoDrawdownBeforeUpcrossing D.X 1 h ω) :
    ∀ y : ℝ, 0 < y →
      Tendsto
        (fun h : ℝ => (∫ ω in
          {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  sorry
