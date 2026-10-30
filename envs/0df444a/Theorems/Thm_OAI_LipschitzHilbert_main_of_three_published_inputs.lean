-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_main_of_three_published_inputs
-- name    : OAI.LipschitzHilbert.main_of_three_published_inputs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:43:54.531+00:00
-- url     : https://prove2.me/theorems/1d0ffc8c-75e9-4563-8b67-b39eb2ae79c0
-- title:
--   OAI.LipschitzHilbert.main_of_three_published_inputs: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.main_of_three_published_inputs` of [lean/OAI/Analysis/LipschitzHilbert/Estimates/ThreeInputMain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Estimates/ThreeInputMain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert`, with `open MeasureTheory Set`, `open scoped ENNReal NNReal`, `open PacketRepresentation`):
--
--   ```lean
--   theorem main_of_three_published_inputs (hVariation : LepingleInput) (hLL : LaceyLiInput)
--       (hH : HorizontalHilbertInput) :
--       ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.HorizontalHilbertInput`, `OAI.LipschitzHilbert.LaceyLiInput` and `OAI.LipschitzHilbert.LepingleInput` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.ShortHilbertConclusion` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.main` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Estimates/ThreeInputMain.lean (declaration OAI.LipschitzHilbert.main_of_three_published_inputs)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem main_of_three_published_inputs (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C := by
  sorry

end LipschitzHilbert

end

end OAI
end
