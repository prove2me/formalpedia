-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3725
-- name    : OAI.UniversalTensorSquare.sg3725
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T14:16:01.046462+00:00
-- url     : https://prove2.me/theorems/40fca498-ea17-4e68-9e24-0c929db498c8
-- title:
--   OAI.UniversalTensorSquare.sg3725: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3725` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes8.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes8.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3725 : RowSquare [9,3,2,1] [3,3,3,3,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg15773`, `OAI.UniversalTensorSquare.sg15790`, `OAI.UniversalTensorSquare.sg34225`, `OAI.UniversalTensorSquare.sg34498`, `OAI.UniversalTensorSquare.sg35151`, `OAI.UniversalTensorSquare.sg35206`, `OAI.UniversalTensorSquare.sg35276`, `OAI.UniversalTensorSquare.sg36898`, `OAI.UniversalTensorSquare.sg37436`, `OAI.UniversalTensorSquare.sg37593`, `OAI.UniversalTensorSquare.sg37600`, `OAI.UniversalTensorSquare.sg37630`, `OAI.UniversalTensorSquare.sg38836`, `OAI.UniversalTensorSquare.sg39453`, `OAI.UniversalTensorSquare.sg39483`, `OAI.UniversalTensorSquare.sg39809`, `OAI.UniversalTensorSquare.sg39909`, `OAI.UniversalTensorSquare.sg39959`, `OAI.UniversalTensorSquare.sg41397`, `OAI.UniversalTensorSquare.sg41463`, `OAI.UniversalTensorSquare.sg41469`, `OAI.UniversalTensorSquare.sg41482`, `OAI.UniversalTensorSquare.sg42054` and `OAI.UniversalTensorSquare.sg42893` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes8.lean (declaration OAI.UniversalTensorSquare.sg3725)

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

lemma sg3725 : RowSquare [9,3,2,1] [3,3,3,3,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
