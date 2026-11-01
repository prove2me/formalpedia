-- Prove2me | Theorems.Thm_OAI_JointDickman_positive_blocks_of_graph_jd
-- name    : OAI.JointDickman.positive_blocks_of_graph_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:33.807173+00:00
-- url     : https://prove2.me/theorems/2832e4c6-150f-4c04-969f-5586c7892d74
-- title:
--   OAI.JointDickman.positive_blocks_of_graph_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.positive_blocks_of_graph` of [lean/OAI/NumberTheory/JointDickman/Counting/PositiveBlockEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/PositiveBlockEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem positive_blocks_of_graph_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
--       {e : ℝ} (he : 0 < e) :
--       ∃ A : ℕ, 0 < A ∧ ∀ (L : ℕ) (τ C : ℝ) (r : ℕ → ℕ), StrictMono r →
--         ∀ F : ℕ → ℕ → ℂ, (∀ N n, ‖F N n‖ ≤ 2) →
--         (∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
--           e ≤ arithmeticOffDiagonalGraph B L τ C (amplificationMultiplier B) (r N) (F (r N)) /
--             ((B : ℝ)*amplificationMultiplier B)) →
--         ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
--           e/2 ≤ arithmeticBlockAverage B L τ C (amplificationMultiplier B) (r N)
--             (amplificationMultiplier B/A) (A*amplificationMultiplier B) (F (r N))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.amplificationMultiplier`, `OAI.JointDickman.arithmeticBlockAverage`, `OAI.JointDickman.arithmeticOffDiagonalGraph`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/PositiveBlockEnergy.lean (declaration OAI.JointDickman.positive_blocks_of_graph)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Filter
open scoped Topology

theorem positive_blocks_of_graph_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {e : ℝ} (he : 0 < e) :
    ∃ A : ℕ, 0 < A ∧ ∀ (L : ℕ) (τ C : ℝ) (r : ℕ → ℕ), StrictMono r →
      ∀ F : ℕ → ℕ → ℂ, (∀ N n, ‖F N n‖ ≤ 2) →
      (∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        e ≤ arithmeticOffDiagonalGraph B L τ C (amplificationMultiplier B) (r N) (F (r N)) /
          ((B : ℝ)*amplificationMultiplier B)) →
      ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        e/2 ≤ arithmeticBlockAverage B L τ C (amplificationMultiplier B) (r N)
          (amplificationMultiplier B/A) (A*amplificationMultiplier B) (F (r N)) := by
  sorry

end JointDickman

end OAI
end
