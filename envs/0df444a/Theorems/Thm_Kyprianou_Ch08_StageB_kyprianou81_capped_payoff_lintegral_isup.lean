-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_kyprianou81_capped_payoff_lintegral_isup
-- name    : Kyprianou.Ch08.StageB.kyprianou81_capped_payoff_lintegral_isup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T02:36:03.074977+00:00
-- url     : https://prove2.me/theorems/3cc4b661-041f-45e7-9eee-df9cc9c7e425
-- title:
--   Capped stopped payoff integrals increase to the uncapped stopped payoff
-- statement:
--   For a spectrally negative Levy process with two-sided exit clocks U (upper) and L (lower), and arbitrary measurable nonnegative discount and path-reward functions, the lower-integral of the uncapped upper-before-lower stopped payoff equals the supremum over n of the capped integrals that additionally require U<=n and evaluate the shifted reward at the capped clock (min U n).toNNReal. On each capped event the capped clock agrees with U, and every upper-before-lower path is eventually capped, so monotone convergence applies.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.kyprianou81_capped_payoff_lintegral_isup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discountE : ℝ≥0 → ℝ≥0∞) (hdE : Measurable discountE)
    (rewardE : (ℝ≥0 → ℝ) → ℝ≥0∞) (hrE : Measurable rewardE) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let A : ℕ → Set Ω := fun n => {ω | U ω < L ω} ∩ {ω | U ω ≤ (n : ℝ≥0∞)}
    let τ : ℕ → Ω → ℝ≥0 := fun n ω => (min (U ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
    let Fc : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ A n then discountE (τ n ω) *
      rewardE (fun t : ℝ≥0 => X.X (τ n ω + t) ω - X.X (τ n ω) ω) else 0
    (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) *
      rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) = ⨆ n, (∫⁻ ω, Fc n ω ∂P) := by
  sorry
