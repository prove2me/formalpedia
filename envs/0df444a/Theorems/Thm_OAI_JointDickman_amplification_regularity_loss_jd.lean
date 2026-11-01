-- Prove2me | Theorems.Thm_OAI_JointDickman_amplification_regularity_loss_jd
-- name    : OAI.JointDickman.amplification_regularity_loss_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:22:30.194838+00:00
-- url     : https://prove2.me/theorems/076c8c74-fe37-4114-b5a9-7b80302a33dc
-- title:
--   OAI.JointDickman.amplification_regularity_loss_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.amplification_regularity_loss` of [lean/OAI/NumberTheory/JointDickman/Amplification/AmplificationRegularity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/AmplificationRegularity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Filter Finset`, `open scoped Topology`):
--
--   ```lean
--   theorem amplification_regularity_loss_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput) :
--       ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
--         ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
--           ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), 0 ≤ C → 0 < T →
--             (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
--             (B : ℝ) * fairFourSubsetFailure B L T τ C ≤
--               K * (ε B + Real.exp (-(1 / 10 : ℝ) * C))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.fairFourSubsetFailure`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/AmplificationRegularity.lean (declaration OAI.JointDickman.amplification_regularity_loss)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman

open Filter Finset
open scoped Topology

theorem amplification_regularity_loss_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), 0 ≤ C → 0 < T →
          (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
          (B : ℝ) * fairFourSubsetFailure B L T τ C ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  sorry

end JointDickman

end OAI
end
