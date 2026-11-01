-- Prove2me | Theorems.Thm_OAI_JointDickman_coefficient_frozen_fullArc_integral_law_jd
-- name    : OAI.JointDickman.coefficient_frozen_fullArc_integral_law_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:24:42.592885+00:00
-- url     : https://prove2.me/theorems/78a686b6-49fc-4de9-b0a7-de4f59afed40
-- title:
--   OAI.JointDickman.coefficient_frozen_fullArc_integral_law_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.coefficient_frozen_fullArc_integral_law` of [lean/OAI/NumberTheory/JointDickman/Amplification/FrozenFullArcIntegral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/FrozenFullArcIntegral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Filter MeasureTheory Function`, `open scoped Topology ArithmeticFunction.Moebius SchwartzMap`):
--
--   ```lean
--   theorem coefficient_frozen_fullArc_integral_law_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput) :
--       ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
--         ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
--         ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
--         Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
--         ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
--         ∀ (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
--         (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
--         (∀ x, |w x| ≤ M) → (∀ x, |w' x| ≤ N) →
--         (∀ x, x ≤ a ∨ b < x → w x = 0) →
--         ∀ F G : ℝ → ℂ, Continuous F → Continuous G → Periodic F 1 → Periodic G 1 →
--         ∀ MF MG : ℝ, 0 ≤ MF → 0 ≤ MG → (∀ x, ‖F x‖ ≤ MF) → (∀ x, ‖G x‖ ≤ MG) →
--         ‖(∫ x in smallMajorArcRegion B j X Q,
--             F x*G x*smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w)-
--           fullSmallMajorArcModel B j X Q (fun x => F x*G x) ((fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ))
--             (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))‖ ≤
--           (X*((K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*(B : ℝ)^(-50 : ℝ)+C*M/B))/2*
--             ((∫ x in (0 : ℝ)..1, ‖F x‖^2)+(∫ x in (0 : ℝ)..1, ‖G x‖^2))+
--           ((B^12 : ℕ) : ℝ)*((B^12 : ℕ)+1)*
--             ((MF*MG)*(((B : ℝ)^13)^10)⁻¹*|coefficientDensity c H B (Real.log X/B)| *
--               (∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.coefficientDensity`, `OAI.JointDickman.fullSmallMajorArcModel`, `OAI.JointDickman.smallMajorArcRegion`, `OAI.JointDickman.smoothCoefficientAdditiveSum`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.testFourierTransform`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.weighted_geometric_period_model_vanishing_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/FrozenFullArcIntegral.lean (declaration OAI.JointDickman.coefficient_frozen_fullArc_integral_law)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Filter MeasureTheory Function
open scoped Topology ArithmeticFunction.Moebius SchwartzMap

theorem coefficient_frozen_fullArc_integral_law_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M) → (∀ x, |w' x| ≤ N) →
      (∀ x, x ≤ a ∨ b < x → w x = 0) →
      ∀ F G : ℝ → ℂ, Continuous F → Continuous G → Periodic F 1 → Periodic G 1 →
      ∀ MF MG : ℝ, 0 ≤ MF → 0 ≤ MG → (∀ x, ‖F x‖ ≤ MF) → (∀ x, ‖G x‖ ≤ MG) →
      ‖(∫ x in smallMajorArcRegion B j X Q,
          F x*G x*smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w)-
        fullSmallMajorArcModel B j X Q (fun x => F x*G x) ((fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ))
          (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))‖ ≤
        (X*((K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*(B : ℝ)^(-50 : ℝ)+C*M/B))/2*
          ((∫ x in (0 : ℝ)..1, ‖F x‖^2)+(∫ x in (0 : ℝ)..1, ‖G x‖^2))+
        ((B^12 : ℕ) : ℝ)*((B^12 : ℕ)+1)*
          ((MF*MG)*(((B : ℝ)^13)^10)⁻¹*|coefficientDensity c H B (Real.log X/B)| *
            (∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖)) := by
  sorry

end JointDickman

end OAI
end
