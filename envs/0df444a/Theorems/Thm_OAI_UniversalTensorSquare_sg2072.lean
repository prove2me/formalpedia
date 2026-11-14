-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2072
-- name    : OAI.UniversalTensorSquare.sg2072
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T21:55:29.037307+00:00
-- url     : https://prove2.me/theorems/6b41400e-ee5a-4af0-953b-acaea63eb693
-- title:
--   OAI.UniversalTensorSquare.sg2072: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2072` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2072 : RowSquare [4,3,1,1,1,1,1,1] [13]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg12948`, `OAI.UniversalTensorSquare.sg12960`, `OAI.UniversalTensorSquare.sg12966`, `OAI.UniversalTensorSquare.sg26992`, `OAI.UniversalTensorSquare.sg27026`, `OAI.UniversalTensorSquare.sg27644`, `OAI.UniversalTensorSquare.sg27703`, `OAI.UniversalTensorSquare.sg27712`, `OAI.UniversalTensorSquare.sg27713`, `OAI.UniversalTensorSquare.sg27762`, `OAI.UniversalTensorSquare.sg27771`, `OAI.UniversalTensorSquare.sg27944`, `OAI.UniversalTensorSquare.sg27953` and `OAI.UniversalTensorSquare.sg30763` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg2072)

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

lemma sg2072 : RowSquare [4,3,1,1,1,1,1,1] [13] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
