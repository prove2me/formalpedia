-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg551
-- name    : OAI.UniversalTensorSquare.sg551
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:43:59.694193+00:00
-- url     : https://prove2.me/theorems/6f7caf14-ad55-4aa9-b064-ad8fee7d1804
-- title:
--   OAI.UniversalTensorSquare.sg551: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg551` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg551 : RowSquare [4,2,2,1] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.sg29902`, `OAI.UniversalTensorSquare.sg32403`, `OAI.UniversalTensorSquare.sg32603`, `OAI.UniversalTensorSquare.sg32646`, `OAI.UniversalTensorSquare.sg33289`, `OAI.UniversalTensorSquare.sg33331`, `OAI.UniversalTensorSquare.sg34349`, `OAI.UniversalTensorSquare.sg34350`, `OAI.UniversalTensorSquare.sg34351`, `OAI.UniversalTensorSquare.sg34353`, `OAI.UniversalTensorSquare.sg34389`, `OAI.UniversalTensorSquare.sg34391`, `OAI.UniversalTensorSquare.sg34392`, `OAI.UniversalTensorSquare.sg34394`, `OAI.UniversalTensorSquare.sg34496`, `OAI.UniversalTensorSquare.sg35034`, `OAI.UniversalTensorSquare.sg35038`, `OAI.UniversalTensorSquare.sg35040`, `OAI.UniversalTensorSquare.sg35182`, `OAI.UniversalTensorSquare.sg35195`, `OAI.UniversalTensorSquare.sg35217`, `OAI.UniversalTensorSquare.sg35335`, `OAI.UniversalTensorSquare.sg35345`, `OAI.UniversalTensorSquare.sg35346`, `OAI.UniversalTensorSquare.sg35349`, `OAI.UniversalTensorSquare.sg35350`, `OAI.UniversalTensorSquare.sg35351`, `OAI.UniversalTensorSquare.sg35362`, `OAI.UniversalTensorSquare.sg35365`, `OAI.UniversalTensorSquare.sg35415`, `OAI.UniversalTensorSquare.sg35434`, `OAI.UniversalTensorSquare.sg35435`, `OAI.UniversalTensorSquare.sg35438`, `OAI.UniversalTensorSquare.sg4979` and `OAI.UniversalTensorSquare.sg8467` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg551)

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

lemma sg551 : RowSquare [4,2,2,1] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
