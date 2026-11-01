-- Prove2me | Theorems.Thm_OAI_JointDickman_weighted_geometric_period_model_vanishing_jd
-- name    : OAI.JointDickman.weighted_geometric_period_model_vanishing_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:37:58.460174+00:00
-- url     : https://prove2.me/theorems/ece22327-7237-4bf5-bcf7-6a02baeddd58
-- title:
--   OAI.JointDickman.weighted_geometric_period_model_vanishing_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.weighted_geometric_period_model_vanishing` of [lean/OAI/NumberTheory/JointDickman/Amplification/WeightedPeriodLaw.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/WeightedPeriodLaw.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory`, `open scoped Topology SchwartzMap`):
--
--   ```lean
--   theorem weighted_geometric_period_model_vanishing_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
--       (ht : 0 < t) (hη : 0 < η)
--       (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) {M M₀ D₀ R : ℝ}
--       (hR : 0 ≤ R)
--       (hM0 : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
--       (hw₁ : ∀ x, |w₁ x| ≤ M) (hw₂ : ∀ x, |w₂ x| ≤ M)
--       (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
--       (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
--       (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
--       ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
--         ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
--         ∀ T : ℝ, 0 < T → η*T ≤ B → ∀ S : Finset ℤ,
--         (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
--         (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
--           Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
--         ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
--         ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q →
--         ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
--         (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
--         let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
--         T*‖weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w-
--           geometricFullArcSum B j Q a b T t S (fun k => r k*d k) g h w₁ w₂ w‖ ≤ ε B
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.coefficientDensity`, `OAI.JointDickman.geometricFullArcSum`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.weightedGeometricPeriodSum` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.amplification_positive_mass_bound_jd` and `OAI.JointDickman.counting_arithmetic_feature_comparison_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/WeightedPeriodLaw.lean (declaration OAI.JointDickman.weighted_geometric_period_model_vanishing)

import Mathlib
import Definitions.Def_OAIQ083J003

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

theorem weighted_geometric_period_model_vanishing_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) {M M₀ D₀ R : ℝ}
    (hR : 0 ≤ R)
    (hM0 : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, |w₁ x| ≤ M) (hw₂ : ∀ x, |w₂ x| ≤ M)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℝ, 0 < T → η*T ≤ B → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      T*‖weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w-
        geometricFullArcSum B j Q a b T t S (fun k => r k*d k) g h w₁ w₂ w‖ ≤ ε B := by
  sorry

end JointDickman

end OAI
end
