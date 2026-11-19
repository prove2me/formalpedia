-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg903
-- name    : OAI.UniversalTensorSquare.sg903
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:55:59.814425+00:00
-- url     : https://prove2.me/theorems/35c45292-c26a-4295-a17d-b61ab9f2c679
-- title:
--   OAI.UniversalTensorSquare.sg903: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg903` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg903 : RowSquare [5,1,1,1,1,1] [4,4,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg10295`, `OAI.UniversalTensorSquare.sg10501`, `OAI.UniversalTensorSquare.sg1340`, `OAI.UniversalTensorSquare.sg26317`, `OAI.UniversalTensorSquare.sg30302`, `OAI.UniversalTensorSquare.sg34471`, `OAI.UniversalTensorSquare.sg34474`, `OAI.UniversalTensorSquare.sg39549`, `OAI.UniversalTensorSquare.sg5632`, `OAI.UniversalTensorSquare.sg5633`, `OAI.UniversalTensorSquare.sg7649`, `OAI.UniversalTensorSquare.sg7654`, `OAI.UniversalTensorSquare.sg7655`, `OAI.UniversalTensorSquare.sg7656`, `OAI.UniversalTensorSquare.sg7715`, `OAI.UniversalTensorSquare.sg7718`, `OAI.UniversalTensorSquare.sg7719`, `OAI.UniversalTensorSquare.sg8715` and `OAI.UniversalTensorSquare.sg9835` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg903)

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

lemma sg903 : RowSquare [5,1,1,1,1,1] [4,4,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
