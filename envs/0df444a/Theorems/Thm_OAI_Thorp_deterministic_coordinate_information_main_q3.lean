-- Prove2me | Theorems.Thm_OAI_Thorp_deterministic_coordinate_information_main_q3
-- name    : OAI.Thorp.deterministic_coordinate_information_main_q3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T03:02:13.134624+00:00
-- url     : https://prove2.me/theorems/00e50dd7-cfef-4286-a4ed-3796354ade48
-- title:
--   OAI.Thorp.deterministic_coordinate_information_main_q3: intermediate lemma from OpenAI, Optimal-order mixing of the Thorp shuffle
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpResults.remaining_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal-order mixing of the Thorp shuffle*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Thorp.deterministic_coordinate_information_main` of [lean/OAI/Probability/ThorpResults/ThorpResults/Mixing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpResults/ThorpResults/Mixing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Thorp`, with `open Filter`):
--
--   ```lean
--   theorem deterministic_coordinate_information_main_q3 :
--       (∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
--         ∀ k : ℕ, 8 * k ≤ 7 * 2 ^ d →
--         ∀ (start : State d) (labels : LabelList d k),
--           listTV (256 * d) start labels < ε) ∧
--       (∀ᶠ d : ℕ in atTop,
--         ∀ k : ℕ, 16 * k ≤ 15 * 2 ^ d →
--         ∀ (start : State d) (labels : LabelList d k),
--           listTV (1024 * d) start labels ≤ Real.rpow ((2 : ℝ) ^ d) (-(3 : ℝ) / 2)) ∧
--       (Tendsto (fun d : ℕ => distance d (2048 * d)) atTop (nhds 0) ∧
--         ∀ (d : ℕ) (start : State d),
--           tv (lawFrom d (2048 * d) start) (uniform d) = distance d (2048 * d))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Thorp.LabelList`, `OAI.Thorp.Position`, `OAI.Thorp.State`, `OAI.Thorp.distance`, `OAI.Thorp.lawFrom`, `OAI.Thorp.listTV`, `OAI.Thorp.tv` and `OAI.Thorp.uniform` (the published bundle `Def_ThorpRemaining`).
--
--   **Used by.** The proof of `OAI.ThorpResults.remaining_main` of this split imports it.
-- source:
--   OpenAI, Optimal-order mixing of the Thorp shuffle, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpResults/ThorpResults/Mixing.lean (declaration OAI.Thorp.deterministic_coordinate_information_main)

import Mathlib
import Definitions.Def_ThorpRemaining

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter

namespace Thorp

theorem deterministic_coordinate_information_main_q3 :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
      ∀ k : ℕ, 8 * k ≤ 7 * 2 ^ d →
      ∀ (start : State d) (labels : LabelList d k),
        listTV (256 * d) start labels < ε) ∧
    (∀ᶠ d : ℕ in atTop,
      ∀ k : ℕ, 16 * k ≤ 15 * 2 ^ d →
      ∀ (start : State d) (labels : LabelList d k),
        listTV (1024 * d) start labels ≤ Real.rpow ((2 : ℝ) ^ d) (-(3 : ℝ) / 2)) ∧
    (Tendsto (fun d : ℕ => distance d (2048 * d)) atTop (nhds 0) ∧
      ∀ (d : ℕ) (start : State d),
        tv (lawFrom d (2048 * d) start) (uniform d) = distance d (2048 * d)) := by
  sorry

end Thorp

end OAI
end
