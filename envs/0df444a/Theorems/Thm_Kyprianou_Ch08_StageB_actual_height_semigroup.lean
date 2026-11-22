-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_semigroup
-- name    : Kyprianou.Ch08.StageB.actual_height_semigroup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:34:23.189706+00:00
-- url     : https://prove2.me/theorems/47fdba96-7849-46b6-87b0-6cea26c5eadd
-- title:
--   Theorem 8.2 actual-height semigroup law: fixed-height strong-Markov split
-- statement:
--   Under the exact hypotheses of Theorem 8.2, the no-drawdown survival functional satisfies the fixed-height semigroup identity S(a1+a2,h) = S(a1,h) * S(a2,h). This is the strong-Markov core from which the T3 exponential identity follows via sibling tail-bounds positivity (T1) and Cauchy analysis.
-- source:
--   Source-faithful decomposition child of Kyprianou Chapter 8 Theorem 8.2 actual-height multiplicative law (parent 027be585-204d-4aae-93f8-d5329c6a8b14): isolates the fixed-height strong-Markov split with the exact original-path event and payoff from Definitions.Def_Kyprianou_Ch08_StageCFoundation_D.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_semigroup
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ a1 a2 h : ℝ, 0 < a1 → 0 < a2 → 0 < h →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X (a1 + a2) h ω}, Real.exp (Phi ψ q * (a1 + a2)) * discountedAt q (tauPlus D.X (a1 + a2) ω) ∂P) =
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a1 h ω}, Real.exp (Phi ψ q * a1) * discountedAt q (tauPlus D.X a1 ω) ∂P) *
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a2 h ω}, Real.exp (Phi ψ q * a2) * discountedAt q (tauPlus D.X a2 ω) ∂P) := by
  sorry
