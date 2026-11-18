-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg489
-- name    : OAI.UniversalTensorSquare.sg489
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:35:22.79389+00:00
-- url     : https://prove2.me/theorems/2f968131-3fdc-42a1-a2a9-5e52236c0dfc
-- title:
--   OAI.UniversalTensorSquare.sg489: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg489` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg489 : RowSquare [3,3,1,1,1] [2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_891All`, `OAI.UniversalTensorSquare.degreeTree62_917All`, `OAI.UniversalTensorSquare.sg36728`, `OAI.UniversalTensorSquare.sg36755`, `OAI.UniversalTensorSquare.sg36757`, `OAI.UniversalTensorSquare.sg36759`, `OAI.UniversalTensorSquare.sg39588`, `OAI.UniversalTensorSquare.sg39605`, `OAI.UniversalTensorSquare.sg39608`, `OAI.UniversalTensorSquare.sg39609`, `OAI.UniversalTensorSquare.sg40553`, `OAI.UniversalTensorSquare.sg40598`, `OAI.UniversalTensorSquare.sg40619`, `OAI.UniversalTensorSquare.sg40985`, `OAI.UniversalTensorSquare.sg41031`, `OAI.UniversalTensorSquare.sg41032`, `OAI.UniversalTensorSquare.sg41034`, `OAI.UniversalTensorSquare.sg41059`, `OAI.UniversalTensorSquare.sg41060`, `OAI.UniversalTensorSquare.sg41062`, `OAI.UniversalTensorSquare.sg41190`, `OAI.UniversalTensorSquare.sg41192`, `OAI.UniversalTensorSquare.sg41193`, `OAI.UniversalTensorSquare.sg41223`, `OAI.UniversalTensorSquare.sg41224`, `OAI.UniversalTensorSquare.sg41234`, `OAI.UniversalTensorSquare.sg41236`, `OAI.UniversalTensorSquare.sg41237`, `OAI.UniversalTensorSquare.sg41256`, `OAI.UniversalTensorSquare.sg41277`, `OAI.UniversalTensorSquare.sg41278`, `OAI.UniversalTensorSquare.sg41280`, `OAI.UniversalTensorSquare.sg41301`, `OAI.UniversalTensorSquare.sg41302`, `OAI.UniversalTensorSquare.sg41346`, `OAI.UniversalTensorSquare.sg41347`, `OAI.UniversalTensorSquare.sg41349`, `OAI.UniversalTensorSquare.sg41363`, `OAI.UniversalTensorSquare.sg42120`, `OAI.UniversalTensorSquare.sg42226`, `OAI.UniversalTensorSquare.sg42578`, `OAI.UniversalTensorSquare.sg42804`, `OAI.UniversalTensorSquare.sg42807`, `OAI.UniversalTensorSquare.sg42872`, `OAI.UniversalTensorSquare.sg42879`, `OAI.UniversalTensorSquare.sg42929`, `OAI.UniversalTensorSquare.sg42937`, `OAI.UniversalTensorSquare.sg42943`, `OAI.UniversalTensorSquare.sg42944`, `OAI.UniversalTensorSquare.sg42952`, `OAI.UniversalTensorSquare.sg42967`, `OAI.UniversalTensorSquare.sg42968`, `OAI.UniversalTensorSquare.sg42970`, `OAI.UniversalTensorSquare.sg42977`, `OAI.UniversalTensorSquare.sg42978`, `OAI.UniversalTensorSquare.sg43041`, `OAI.UniversalTensorSquare.sg43092`, `OAI.UniversalTensorSquare.sg43103`, `OAI.UniversalTensorSquare.sg43155`, `OAI.UniversalTensorSquare.sg43159`, `OAI.UniversalTensorSquare.sg43166` and `OAI.UniversalTensorSquare.sg43213` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg489)

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

lemma sg489 : RowSquare [3,3,1,1,1] [2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
