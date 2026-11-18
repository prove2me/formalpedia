-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg480
-- name    : OAI.UniversalTensorSquare.sg480
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:35:14.411485+00:00
-- url     : https://prove2.me/theorems/decac933-0878-47ff-9b4d-81036ae1c231
-- title:
--   OAI.UniversalTensorSquare.sg480: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg480` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg480 : RowSquare [3,2,2,2] [2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg13163`, `OAI.UniversalTensorSquare.sg15748`, `OAI.UniversalTensorSquare.sg33709`, `OAI.UniversalTensorSquare.sg34129`, `OAI.UniversalTensorSquare.sg34161`, `OAI.UniversalTensorSquare.sg34320`, `OAI.UniversalTensorSquare.sg34679`, `OAI.UniversalTensorSquare.sg34831`, `OAI.UniversalTensorSquare.sg34863`, `OAI.UniversalTensorSquare.sg34988`, `OAI.UniversalTensorSquare.sg35133`, `OAI.UniversalTensorSquare.sg36835`, `OAI.UniversalTensorSquare.sg37291`, `OAI.UniversalTensorSquare.sg37307`, `OAI.UniversalTensorSquare.sg37308`, `OAI.UniversalTensorSquare.sg37395`, `OAI.UniversalTensorSquare.sg37436`, `OAI.UniversalTensorSquare.sg37492`, `OAI.UniversalTensorSquare.sg37493`, `OAI.UniversalTensorSquare.sg38179`, `OAI.UniversalTensorSquare.sg38440`, `OAI.UniversalTensorSquare.sg38545`, `OAI.UniversalTensorSquare.sg38582`, `OAI.UniversalTensorSquare.sg38681`, `OAI.UniversalTensorSquare.sg39328`, `OAI.UniversalTensorSquare.sg39362`, `OAI.UniversalTensorSquare.sg39619`, `OAI.UniversalTensorSquare.sg39695`, `OAI.UniversalTensorSquare.sg39748`, `OAI.UniversalTensorSquare.sg39787`, `OAI.UniversalTensorSquare.sg39856`, `OAI.UniversalTensorSquare.sg40057`, `OAI.UniversalTensorSquare.sg40646`, `OAI.UniversalTensorSquare.sg41070`, `OAI.UniversalTensorSquare.sg41287`, `OAI.UniversalTensorSquare.sg41317`, `OAI.UniversalTensorSquare.sg41372`, `OAI.UniversalTensorSquare.sg41379`, `OAI.UniversalTensorSquare.sg41397`, `OAI.UniversalTensorSquare.sg41731`, `OAI.UniversalTensorSquare.sg41891` and `OAI.UniversalTensorSquare.sg41988` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg480)

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

lemma sg480 : RowSquare [3,2,2,2] [2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
