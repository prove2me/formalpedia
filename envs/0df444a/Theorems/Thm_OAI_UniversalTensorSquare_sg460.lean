-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg460
-- name    : OAI.UniversalTensorSquare.sg460
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:16:47.703203+00:00
-- url     : https://prove2.me/theorems/0e005dec-18c8-45f8-bbec-6ca3585187c2
-- title:
--   OAI.UniversalTensorSquare.sg460: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg460` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg460 : RowSquare [3,2,1,1,1,1] [4,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_357All`, `OAI.UniversalTensorSquare.degreeTree62_405All`, `OAI.UniversalTensorSquare.degreeTree62_412All`, `OAI.UniversalTensorSquare.sg18654`, `OAI.UniversalTensorSquare.sg18660`, `OAI.UniversalTensorSquare.sg18670`, `OAI.UniversalTensorSquare.sg18728`, `OAI.UniversalTensorSquare.sg18790`, `OAI.UniversalTensorSquare.sg28380`, `OAI.UniversalTensorSquare.sg35939`, `OAI.UniversalTensorSquare.sg35942`, `OAI.UniversalTensorSquare.sg35944`, `OAI.UniversalTensorSquare.sg36011`, `OAI.UniversalTensorSquare.sg36013`, `OAI.UniversalTensorSquare.sg36015`, `OAI.UniversalTensorSquare.sg36147`, `OAI.UniversalTensorSquare.sg36174`, `OAI.UniversalTensorSquare.sg36176`, `OAI.UniversalTensorSquare.sg36178`, `OAI.UniversalTensorSquare.sg36449`, `OAI.UniversalTensorSquare.sg36452`, `OAI.UniversalTensorSquare.sg36454`, `OAI.UniversalTensorSquare.sg36490`, `OAI.UniversalTensorSquare.sg36512`, `OAI.UniversalTensorSquare.sg36515`, `OAI.UniversalTensorSquare.sg36517`, `OAI.UniversalTensorSquare.sg36650`, `OAI.UniversalTensorSquare.sg36680`, `OAI.UniversalTensorSquare.sg36682`, `OAI.UniversalTensorSquare.sg36684`, `OAI.UniversalTensorSquare.sg40426`, `OAI.UniversalTensorSquare.sg40428`, `OAI.UniversalTensorSquare.sg40429`, `OAI.UniversalTensorSquare.sg40812`, `OAI.UniversalTensorSquare.sg40814`, `OAI.UniversalTensorSquare.sg40815` and `OAI.UniversalTensorSquare.sg4091` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg460)

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

lemma sg460 : RowSquare [3,2,1,1,1,1] [4,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
