-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg458
-- name    : OAI.UniversalTensorSquare.sg458
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:16:37.638455+00:00
-- url     : https://prove2.me/theorems/5e1c7d1b-1e69-447b-a7aa-845319b30a48
-- title:
--   OAI.UniversalTensorSquare.sg458: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg458` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg458 : RowSquare [3,2,1,1,1,1] [3,3,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_578All`, `OAI.UniversalTensorSquare.degreeTree62_581All`, `OAI.UniversalTensorSquare.degreeTree62_631All`, `OAI.UniversalTensorSquare.degreeTree62_653All`, `OAI.UniversalTensorSquare.degreeTree62_688All`, `OAI.UniversalTensorSquare.degreeTree62_727All`, `OAI.UniversalTensorSquare.sg18724`, `OAI.UniversalTensorSquare.sg36637`, `OAI.UniversalTensorSquare.sg36642`, `OAI.UniversalTensorSquare.sg36644`, `OAI.UniversalTensorSquare.sg37789`, `OAI.UniversalTensorSquare.sg37794`, `OAI.UniversalTensorSquare.sg37796`, `OAI.UniversalTensorSquare.sg38004`, `OAI.UniversalTensorSquare.sg38007`, `OAI.UniversalTensorSquare.sg38009`, `OAI.UniversalTensorSquare.sg39220`, `OAI.UniversalTensorSquare.sg40080`, `OAI.UniversalTensorSquare.sg40082`, `OAI.UniversalTensorSquare.sg40083`, `OAI.UniversalTensorSquare.sg42125` and `OAI.UniversalTensorSquare.sg42132` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg458)

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

lemma sg458 : RowSquare [3,2,1,1,1,1] [3,3,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
