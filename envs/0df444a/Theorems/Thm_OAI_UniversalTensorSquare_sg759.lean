-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg759
-- name    : OAI.UniversalTensorSquare.sg759
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:22:13.70333+00:00
-- url     : https://prove2.me/theorems/c24c4c45-bf01-4246-83cb-8419ec349ba8
-- title:
--   OAI.UniversalTensorSquare.sg759: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg759` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg759 : RowSquare [3,2,2,2,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_5All`, `OAI.UniversalTensorSquare.sg15784`, `OAI.UniversalTensorSquare.sg16159`, `OAI.UniversalTensorSquare.sg16168`, `OAI.UniversalTensorSquare.sg31957`, `OAI.UniversalTensorSquare.sg32064`, `OAI.UniversalTensorSquare.sg32066`, `OAI.UniversalTensorSquare.sg32068`, `OAI.UniversalTensorSquare.sg32073`, `OAI.UniversalTensorSquare.sg32825`, `OAI.UniversalTensorSquare.sg32826`, `OAI.UniversalTensorSquare.sg32963`, `OAI.UniversalTensorSquare.sg33011`, `OAI.UniversalTensorSquare.sg33110`, `OAI.UniversalTensorSquare.sg33158`, `OAI.UniversalTensorSquare.sg3337`, `OAI.UniversalTensorSquare.sg37682`, `OAI.UniversalTensorSquare.sg37683`, `OAI.UniversalTensorSquare.sg39483`, `OAI.UniversalTensorSquare.sg39511`, `OAI.UniversalTensorSquare.sg3992`, `OAI.UniversalTensorSquare.sg4041`, `OAI.UniversalTensorSquare.sg4043`, `OAI.UniversalTensorSquare.sg40753` and `OAI.UniversalTensorSquare.sg4120` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg759)

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

lemma sg759 : RowSquare [3,2,2,2,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
