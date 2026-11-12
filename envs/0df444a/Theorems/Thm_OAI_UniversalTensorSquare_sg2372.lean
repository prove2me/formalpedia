-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2372
-- name    : OAI.UniversalTensorSquare.sg2372
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T01:22:49.897202+00:00
-- url     : https://prove2.me/theorems/d13f1a7d-c03c-4d93-9d3f-41eada29d8ab
-- title:
--   OAI.UniversalTensorSquare.sg2372: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2372` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2372 : RowSquare [8,2,1,1,1] [3,3,3,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_191All`, `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_422All`, `OAI.UniversalTensorSquare.sg12564`, `OAI.UniversalTensorSquare.sg34084`, `OAI.UniversalTensorSquare.sg34089`, `OAI.UniversalTensorSquare.sg34091`, `OAI.UniversalTensorSquare.sg34092`, `OAI.UniversalTensorSquare.sg34094`, `OAI.UniversalTensorSquare.sg34096`, `OAI.UniversalTensorSquare.sg34132`, `OAI.UniversalTensorSquare.sg34140`, `OAI.UniversalTensorSquare.sg34142`, `OAI.UniversalTensorSquare.sg34164`, `OAI.UniversalTensorSquare.sg34170`, `OAI.UniversalTensorSquare.sg34172`, `OAI.UniversalTensorSquare.sg34174`, `OAI.UniversalTensorSquare.sg34709`, `OAI.UniversalTensorSquare.sg34991`, `OAI.UniversalTensorSquare.sg35007`, `OAI.UniversalTensorSquare.sg35956`, `OAI.UniversalTensorSquare.sg38384`, `OAI.UniversalTensorSquare.sg39184`, `OAI.UniversalTensorSquare.sg39545` and `OAI.UniversalTensorSquare.sg40565` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2372)

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

lemma sg2372 : RowSquare [8,2,1,1,1] [3,3,3,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
