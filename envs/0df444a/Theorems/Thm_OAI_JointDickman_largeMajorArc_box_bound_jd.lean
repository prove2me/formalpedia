-- Prove2me | Theorems.Thm_OAI_JointDickman_largeMajorArc_box_bound_jd
-- name    : OAI.JointDickman.largeMajorArc_box_bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:27:46.936465+00:00
-- url     : https://prove2.me/theorems/7c8073a8-2bf9-4bea-b88e-441e00819602
-- title:
--   OAI.JointDickman.largeMajorArc_box_bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.largeMajorArc_box_bound` of [lean/OAI/NumberTheory/JointDickman/Amplification/LargeMajorBoxBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/LargeMajorBoxBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Filter MeasureTheory Finset`, `open scoped Topology`):
--
--   ```lean
--   theorem largeMajorArc_box_bound_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {a b c d ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
--       (hc : 0 < c) (hcd : c ≤ d) (hε : 0 < ε) :
--       ∃ C D K : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ K ∧
--         ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
--         Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
--         Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
--         ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q → ∀ j : ℕ,
--         ∀ g h : Finset ℕ → ℝ,
--         (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
--         (∀ S ⊆ auxiliaryPrimes B, |h S| ≤ 1) →
--         ∀ (w₁ w₂ w₃ w₃' : ℝ → ℝ) (M M₃ N₃ : ℝ),
--         0 ≤ M → 0 ≤ M₃ → 0 ≤ N₃ →
--         (∀ t, |w₁ t| ≤ M) → (∀ t, |w₂ t| ≤ M) →
--         (∀ t, HasDerivAt w₃ (w₃' t) t) → Continuous w₃' →
--         (∀ t, |w₃ t| ≤ M₃) → (∀ t, |w₃' t| ≤ N₃) →
--         (∀ t, t ≤ c ∨ d < t → w₃ t = 0) →
--         ‖(B : ℂ)*(∫ θ in largeMajorArcRegion B j X Q,
--           endpointFourierSum B a b (T*X) g w₁ θ *
--           endpointFourierSum B a b (T*X) h w₂ (-θ) *
--           smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)‖ ≤
--         C*M^2*(D*M₃*(d-c)+K*d*(2*M₃+(N₃+2*Real.pi*M₃)*(d-c)))*
--           (B : ℝ)^(-23/20+ε)/T
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.endpointFourierSum`, `OAI.JointDickman.largeMajorArcRegion`, `OAI.JointDickman.smoothCoefficientAdditiveSum`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.weighted_geometric_period_model_vanishing_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/LargeMajorBoxBound.lean (declaration OAI.JointDickman.largeMajorArc_box_bound)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Filter MeasureTheory Finset
open scoped Topology

theorem largeMajorArc_box_bound_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b c d ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hε : 0 < ε) :
    ∃ C D K : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q → ∀ j : ℕ,
      ∀ g h : Finset ℕ → ℝ,
      (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      (∀ S ⊆ auxiliaryPrimes B, |h S| ≤ 1) →
      ∀ (w₁ w₂ w₃ w₃' : ℝ → ℝ) (M M₃ N₃ : ℝ),
      0 ≤ M → 0 ≤ M₃ → 0 ≤ N₃ →
      (∀ t, |w₁ t| ≤ M) → (∀ t, |w₂ t| ≤ M) →
      (∀ t, HasDerivAt w₃ (w₃' t) t) → Continuous w₃' →
      (∀ t, |w₃ t| ≤ M₃) → (∀ t, |w₃' t| ≤ N₃) →
      (∀ t, t ≤ c ∨ d < t → w₃ t = 0) →
      ‖(B : ℂ)*(∫ θ in largeMajorArcRegion B j X Q,
        endpointFourierSum B a b (T*X) g w₁ θ *
        endpointFourierSum B a b (T*X) h w₂ (-θ) *
        smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)‖ ≤
      C*M^2*(D*M₃*(d-c)+K*d*(2*M₃+(N₃+2*Real.pi*M₃)*(d-c)))*
        (B : ℝ)^(-23/20+ε)/T := by
  sorry

end JointDickman

end OAI
end
