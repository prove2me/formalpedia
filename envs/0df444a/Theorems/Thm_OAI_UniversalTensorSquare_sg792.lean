-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg792
-- name    : OAI.UniversalTensorSquare.sg792
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:28:09.081192+00:00
-- url     : https://prove2.me/theorems/c14c50a9-638c-4a2a-b77e-e22c38ce5ab7
-- title:
--   OAI.UniversalTensorSquare.sg792: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg792` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg792 : RowSquare [3,3,2,1,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_80All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_740All`, `OAI.UniversalTensorSquare.degreeTree62_924All`, `OAI.UniversalTensorSquare.sg26541`, `OAI.UniversalTensorSquare.sg31960`, `OAI.UniversalTensorSquare.sg32322`, `OAI.UniversalTensorSquare.sg32455`, `OAI.UniversalTensorSquare.sg32816`, `OAI.UniversalTensorSquare.sg32819`, `OAI.UniversalTensorSquare.sg33566`, `OAI.UniversalTensorSquare.sg33567`, `OAI.UniversalTensorSquare.sg33568`, `OAI.UniversalTensorSquare.sg33589`, `OAI.UniversalTensorSquare.sg33590`, `OAI.UniversalTensorSquare.sg33593`, `OAI.UniversalTensorSquare.sg33595`, `OAI.UniversalTensorSquare.sg33611`, `OAI.UniversalTensorSquare.sg34000`, `OAI.UniversalTensorSquare.sg36305`, `OAI.UniversalTensorSquare.sg37010`, `OAI.UniversalTensorSquare.sg37251`, `OAI.UniversalTensorSquare.sg37466`, `OAI.UniversalTensorSquare.sg37468`, `OAI.UniversalTensorSquare.sg37693`, `OAI.UniversalTensorSquare.sg37695`, `OAI.UniversalTensorSquare.sg37696`, `OAI.UniversalTensorSquare.sg38292`, `OAI.UniversalTensorSquare.sg38908`, `OAI.UniversalTensorSquare.sg38911`, `OAI.UniversalTensorSquare.sg39981`, `OAI.UniversalTensorSquare.sg39985`, `OAI.UniversalTensorSquare.sg40194`, `OAI.UniversalTensorSquare.sg40748`, `OAI.UniversalTensorSquare.sg41307`, `OAI.UniversalTensorSquare.sg41405`, `OAI.UniversalTensorSquare.sg41408`, `OAI.UniversalTensorSquare.sg41500`, `OAI.UniversalTensorSquare.sg42023`, `OAI.UniversalTensorSquare.sg42025` and `OAI.UniversalTensorSquare.sg42087` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg792)

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

lemma sg792 : RowSquare [3,3,2,1,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
