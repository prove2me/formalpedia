-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg232
-- name    : OAI.UniversalTensorSquare.sg232
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T09:15:24.034504+00:00
-- url     : https://prove2.me/theorems/87dd3c36-0f7f-4a65-a354-9c0ffd221f6b
-- title:
--   OAI.UniversalTensorSquare.sg232: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg232` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg232 : RowSquare [6,1] [5,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_146All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_253All`, `OAI.UniversalTensorSquare.degreeTree62_351All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_827All`, `OAI.UniversalTensorSquare.sg21591`, `OAI.UniversalTensorSquare.sg21667`, `OAI.UniversalTensorSquare.sg2704`, `OAI.UniversalTensorSquare.sg34353`, `OAI.UniversalTensorSquare.sg34391`, `OAI.UniversalTensorSquare.sg34422`, `OAI.UniversalTensorSquare.sg34630`, `OAI.UniversalTensorSquare.sg34637`, `OAI.UniversalTensorSquare.sg34681`, `OAI.UniversalTensorSquare.sg34726`, `OAI.UniversalTensorSquare.sg34739`, `OAI.UniversalTensorSquare.sg34751`, `OAI.UniversalTensorSquare.sg34822`, `OAI.UniversalTensorSquare.sg34879`, `OAI.UniversalTensorSquare.sg34908`, `OAI.UniversalTensorSquare.sg34915`, `OAI.UniversalTensorSquare.sg34991`, `OAI.UniversalTensorSquare.sg35030`, `OAI.UniversalTensorSquare.sg35061`, `OAI.UniversalTensorSquare.sg35154`, `OAI.UniversalTensorSquare.sg35161`, `OAI.UniversalTensorSquare.sg35186`, `OAI.UniversalTensorSquare.sg35213`, `OAI.UniversalTensorSquare.sg35301`, `OAI.UniversalTensorSquare.sg35324`, `OAI.UniversalTensorSquare.sg35396`, `OAI.UniversalTensorSquare.sg35448`, `OAI.UniversalTensorSquare.sg35685`, `OAI.UniversalTensorSquare.sg35979`, `OAI.UniversalTensorSquare.sg36611`, `OAI.UniversalTensorSquare.sg36616`, `OAI.UniversalTensorSquare.sg36648`, `OAI.UniversalTensorSquare.sg36700`, `OAI.UniversalTensorSquare.sg37089`, `OAI.UniversalTensorSquare.sg37799`, `OAI.UniversalTensorSquare.sg37994`, `OAI.UniversalTensorSquare.sg38382`, `OAI.UniversalTensorSquare.sg38564`, `OAI.UniversalTensorSquare.sg38663`, `OAI.UniversalTensorSquare.sg39182`, `OAI.UniversalTensorSquare.sg39346`, `OAI.UniversalTensorSquare.sg40054`, `OAI.UniversalTensorSquare.sg40090`, `OAI.UniversalTensorSquare.sg40378`, `OAI.UniversalTensorSquare.sg40384`, `OAI.UniversalTensorSquare.sg40539`, `OAI.UniversalTensorSquare.sg40790`, `OAI.UniversalTensorSquare.sg40796`, `OAI.UniversalTensorSquare.sg40838`, `OAI.UniversalTensorSquare.sg40956`, `OAI.UniversalTensorSquare.sg41188`, `OAI.UniversalTensorSquare.sg41512`, `OAI.UniversalTensorSquare.sg41539`, `OAI.UniversalTensorSquare.sg41547`, `OAI.UniversalTensorSquare.sg41549`, `OAI.UniversalTensorSquare.sg41647`, `OAI.UniversalTensorSquare.sg41649`, `OAI.UniversalTensorSquare.sg41742` and `OAI.UniversalTensorSquare.sg43047` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg232)

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

lemma sg232 : RowSquare [6,1] [5,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
