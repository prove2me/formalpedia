-- Prove2me | Theorems.Thm_OAI_JointDickman_geometric_sampled_integral_error_sum_jd
-- name    : OAI.JointDickman.geometric_sampled_integral_error_sum_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:27:19.642664+00:00
-- url     : https://prove2.me/theorems/6c0a542e-12d2-41c0-bc21-44862981ff00
-- title:
--   OAI.JointDickman.geometric_sampled_integral_error_sum_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.geometric_sampled_integral_error_sum` of [lean/OAI/NumberTheory/JointDickman/Amplification/GeometricSampledIntegral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/GeometricSampledIntegral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory`, `open scoped Topology SchwartzMap`):
--
--   ```lean
--   theorem geometric_sampled_integral_error_sum_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput) :
--       ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
--         ∀ q : ℕ, [NeZero q] → q ≤ B → ∀ a b t : ℝ, 0 < a → a ≤ b → 0 < t →
--         ∀ S : Finset ℤ, ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
--         (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
--         ∀ (w₁ w₂ w₁' w₂' : ℝ → ℝ) (M₁ M₂ D₁ D₂ β : ℝ),
--         0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ D₁ → 0 ≤ D₂ →
--         (∀ x, HasDerivAt w₁ (w₁' x) x) → (∀ x, HasDerivAt w₂ (w₂' x) x) →
--         (∀ x, |w₁ x| ≤ M₁) → (∀ x, |w₂ x| ≤ M₂) →
--         (∀ x, |w₁' x| ≤ D₁) → (∀ x, |w₂' x| ≤ D₂) →
--         ∀ (P : ZMod q → Prop) [DecidablePred P], ∀ w : 𝓢(ℝ,ℝ),
--         let J := geometricHistogramWindow m B t (Real.log a) (Real.log b)
--         let F := fun k ξ => logOscillatoryTest w₁ B (Real.exp ((k : ℝ)*t)) (β*ξ)
--         let G := fun k ξ => logOscillatoryTest w₂ B (Real.exp ((k : ℝ)*t)) (-β*ξ)
--         let L₁ := (D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))
--         let L₂ := (D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1))
--         (∑ k ∈ S, ‖manuscriptSampledIntegralError m B q (J k) g h (F k) (G k) P w‖) ≤
--           ((q : ℝ)/(q.totient : ℝ))*((Real.log b-Real.log a+2)/B)*C*
--             ((1+Real.log b-Real.log a)/t+1)*
--             (2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
--               2*M₁*M₂*(B : ℝ)^(-(1/80 : ℝ)))*
--             (∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.channelFineCount`, `OAI.JointDickman.channelMesh`, `OAI.JointDickman.geometricHistogramWindow`, `OAI.JointDickman.logOscillatoryTest`, `OAI.JointDickman.manuscriptSampledIntegralError`, `OAI.JointDickman.testFourierTransform`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.bounded_box_coarse_comparison_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/GeometricSampledIntegral.lean (declaration OAI.JointDickman.geometric_sampled_integral_error_sum)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

theorem geometric_sampled_integral_error_sum_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B → ∀ a b t : ℝ, 0 < a → a ≤ b → 0 < t →
      ∀ S : Finset ℤ, ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ (w₁ w₂ w₁' w₂' : ℝ → ℝ) (M₁ M₂ D₁ D₂ β : ℝ),
      0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ D₁ → 0 ≤ D₂ →
      (∀ x, HasDerivAt w₁ (w₁' x) x) → (∀ x, HasDerivAt w₂ (w₂' x) x) →
      (∀ x, |w₁ x| ≤ M₁) → (∀ x, |w₂ x| ≤ M₂) →
      (∀ x, |w₁' x| ≤ D₁) → (∀ x, |w₂' x| ≤ D₂) →
      ∀ (P : ZMod q → Prop) [DecidablePred P], ∀ w : 𝓢(ℝ,ℝ),
      let J := geometricHistogramWindow m B t (Real.log a) (Real.log b)
      let F := fun k ξ => logOscillatoryTest w₁ B (Real.exp ((k : ℝ)*t)) (β*ξ)
      let G := fun k ξ => logOscillatoryTest w₂ B (Real.exp ((k : ℝ)*t)) (-β*ξ)
      let L₁ := (D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))
      let L₂ := (D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1))
      (∑ k ∈ S, ‖manuscriptSampledIntegralError m B q (J k) g h (F k) (G k) P w‖) ≤
        ((q : ℝ)/(q.totient : ℝ))*((Real.log b-Real.log a+2)/B)*C*
          ((1+Real.log b-Real.log a)/t+1)*
          (2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
            2*M₁*M₂*(B : ℝ)^(-(1/80 : ℝ)))*
          (∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|)) := by
  sorry

end JointDickman

end OAI
end
