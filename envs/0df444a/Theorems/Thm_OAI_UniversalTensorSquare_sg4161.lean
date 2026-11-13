-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4161
-- name    : OAI.UniversalTensorSquare.sg4161
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T19:58:49.479203+00:00
-- url     : https://prove2.me/theorems/bd64f142-5182-4b0b-870c-91bd60ae6dad
-- title:
--   OAI.UniversalTensorSquare.sg4161: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4161` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4161 : RowSquare [7,3,2,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_63All`, `OAI.UniversalTensorSquare.degreeTree43_152All`, `OAI.UniversalTensorSquare.degreeTree43_181All`, `OAI.UniversalTensorSquare.degreeTree43_185All`, `OAI.UniversalTensorSquare.degreeTree43_209All`, `OAI.UniversalTensorSquare.degreeTree43_394All`, `OAI.UniversalTensorSquare.degreeTree43_409All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_425All`, `OAI.UniversalTensorSquare.degreeTree43_461All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_500All`, `OAI.UniversalTensorSquare.degreeTree43_502All`, `OAI.UniversalTensorSquare.degreeTree43_508All`, `OAI.UniversalTensorSquare.degreeTree43_510All`, `OAI.UniversalTensorSquare.degreeTree43_511All`, `OAI.UniversalTensorSquare.degreeTree43_520All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree43_561All`, `OAI.UniversalTensorSquare.degreeTree43_646All`, `OAI.UniversalTensorSquare.sg23413`, `OAI.UniversalTensorSquare.sg25826`, `OAI.UniversalTensorSquare.sg25839`, `OAI.UniversalTensorSquare.sg25864`, `OAI.UniversalTensorSquare.sg25940`, `OAI.UniversalTensorSquare.sg25982`, `OAI.UniversalTensorSquare.sg26041`, `OAI.UniversalTensorSquare.sg26066`, `OAI.UniversalTensorSquare.sg26323`, `OAI.UniversalTensorSquare.sg28563`, `OAI.UniversalTensorSquare.sg28662`, `OAI.UniversalTensorSquare.sg28695`, `OAI.UniversalTensorSquare.sg28769`, `OAI.UniversalTensorSquare.sg28775`, `OAI.UniversalTensorSquare.sg28792`, `OAI.UniversalTensorSquare.sg28827`, `OAI.UniversalTensorSquare.sg28927`, `OAI.UniversalTensorSquare.sg29014`, `OAI.UniversalTensorSquare.sg29037`, `OAI.UniversalTensorSquare.sg29089`, `OAI.UniversalTensorSquare.sg29192`, `OAI.UniversalTensorSquare.sg29239`, `OAI.UniversalTensorSquare.sg29243`, `OAI.UniversalTensorSquare.sg29272`, `OAI.UniversalTensorSquare.sg29292`, `OAI.UniversalTensorSquare.sg29364`, `OAI.UniversalTensorSquare.sg29393`, `OAI.UniversalTensorSquare.sg29399`, `OAI.UniversalTensorSquare.sg29454`, `OAI.UniversalTensorSquare.sg29486`, `OAI.UniversalTensorSquare.sg29509`, `OAI.UniversalTensorSquare.sg29558`, `OAI.UniversalTensorSquare.sg29564`, `OAI.UniversalTensorSquare.sg29568`, `OAI.UniversalTensorSquare.sg29583`, `OAI.UniversalTensorSquare.sg29590`, `OAI.UniversalTensorSquare.sg29610`, `OAI.UniversalTensorSquare.sg29647`, `OAI.UniversalTensorSquare.sg29652`, `OAI.UniversalTensorSquare.sg29664`, `OAI.UniversalTensorSquare.sg29685`, `OAI.UniversalTensorSquare.sg29712`, `OAI.UniversalTensorSquare.sg29726`, `OAI.UniversalTensorSquare.sg29785`, `OAI.UniversalTensorSquare.sg29808`, `OAI.UniversalTensorSquare.sg29813`, `OAI.UniversalTensorSquare.sg29825`, `OAI.UniversalTensorSquare.sg29855`, `OAI.UniversalTensorSquare.sg29869`, `OAI.UniversalTensorSquare.sg30004`, `OAI.UniversalTensorSquare.sg30048`, `OAI.UniversalTensorSquare.sg30078`, `OAI.UniversalTensorSquare.sg30095`, `OAI.UniversalTensorSquare.sg30184`, `OAI.UniversalTensorSquare.sg30204`, `OAI.UniversalTensorSquare.sg30235`, `OAI.UniversalTensorSquare.sg30246`, `OAI.UniversalTensorSquare.sg30258`, `OAI.UniversalTensorSquare.sg30278`, `OAI.UniversalTensorSquare.sg30430`, `OAI.UniversalTensorSquare.sg30435`, `OAI.UniversalTensorSquare.sg30481`, `OAI.UniversalTensorSquare.sg30500`, `OAI.UniversalTensorSquare.sg30506`, `OAI.UniversalTensorSquare.sg30520`, `OAI.UniversalTensorSquare.sg30536`, `OAI.UniversalTensorSquare.sg30541`, `OAI.UniversalTensorSquare.sg30741`, `OAI.UniversalTensorSquare.sg30806`, `OAI.UniversalTensorSquare.sg30992`, `OAI.UniversalTensorSquare.sg31517` and `OAI.UniversalTensorSquare.sg31780` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4161)

import Mathlib
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4161 : RowSquare [7,3,2,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
