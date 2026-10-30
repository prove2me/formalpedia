-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_laceyLiInput_proved
-- name    : OAI.LipschitzHilbert.laceyLiInput_proved
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:44:19.826677+00:00
-- url     : https://prove2.me/theorems/2076fba1-28e3-4f3e-810c-954b04d80115
-- title:
--   OAI.LipschitzHilbert.laceyLiInput_proved: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.laceyLiInput_proved` of [lean/OAI/Analysis/LipschitzHilbert/Geometry/LaceyLiProof.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Geometry/LaceyLiProof.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert`, with `open MeasureTheory Set`, `open scoped ENNReal NNReal BigOperators Classical`):
--
--   ```lean
--   theorem laceyLiInput_proved : LaceyLiInput
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LaceyLiInput` (definitions bundle `OAIQ090A000` of this split).
--
--   **Used by.** The proofs of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation` of this split import it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Geometry/LaceyLiProof.lean (declaration OAI.LipschitzHilbert.laceyLiInput_proved)

import Mathlib
import Definitions.Def_OAIQ090A000

section

attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert

theorem laceyLiInput_proved : LaceyLiInput := by
  sorry

end LipschitzHilbert

end

end OAI
end
