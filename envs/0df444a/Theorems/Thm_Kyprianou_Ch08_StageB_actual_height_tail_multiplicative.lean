-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_multiplicative
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_multiplicative
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T19:05:03.217515+00:00
-- url     : https://prove2.me/theorems/027be585-204d-4aae-93f8-d5329c6a8b14
-- title:
--   Theorem 8.2 actual-height multiplicative law: strong-Markov exponential identity
-- statement:
--   Under the exact hypotheses of Theorem 8.2, the no-drawdown survival functional satisfies the exponential identity S(a,h) = exp(-a * F(h)) where F(h) = -log S(1,h). This is the strong-Markov mathematical core of the actual-height law, reducing the level-a integral to the unit-level tail.
-- source:
--   Source-faithful decomposition child of Kyprianou Chapter 8 Theorem 8.2 actual-height law (parent 3eded364-8075-43f9-bae4-12db613bec33): isolates the multiplicative/strong-Markov identity (gap hmult) with the exact original-path event and payoff from Definitions.Def_Kyprianou_Ch08_StageCFoundation_D.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_multiplicative
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω}, Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P) =
      Real.exp (-a * (-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) := by
  sorry
