-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg65
-- name    : OAI.UniversalTensorSquare.sg65
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:25:41.374935+00:00
-- url     : https://prove2.me/theorems/a88aaa90-a634-4671-87b5-7903e49fa1cd
-- title:
--   OAI.UniversalTensorSquare.sg65: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg65` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg65 : RowSquare [2,2,2] [6]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_402All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_521All`, `OAI.UniversalTensorSquare.degreeTree62_524All`, `OAI.UniversalTensorSquare.degreeTree62_627All`, `OAI.UniversalTensorSquare.degreeTree62_869All`, `OAI.UniversalTensorSquare.degreeTree62_971All`, `OAI.UniversalTensorSquare.degreeTree62_973All`, `OAI.UniversalTensorSquare.sg35492`, `OAI.UniversalTensorSquare.sg35494`, `OAI.UniversalTensorSquare.sg35496`, `OAI.UniversalTensorSquare.sg35676`, `OAI.UniversalTensorSquare.sg35710`, `OAI.UniversalTensorSquare.sg36361`, `OAI.UniversalTensorSquare.sg36371`, `OAI.UniversalTensorSquare.sg36375`, `OAI.UniversalTensorSquare.sg36377`, `OAI.UniversalTensorSquare.sg36384`, `OAI.UniversalTensorSquare.sg36386`, `OAI.UniversalTensorSquare.sg36388`, `OAI.UniversalTensorSquare.sg38061`, `OAI.UniversalTensorSquare.sg38062`, `OAI.UniversalTensorSquare.sg38382`, `OAI.UniversalTensorSquare.sg38401`, `OAI.UniversalTensorSquare.sg38402`, `OAI.UniversalTensorSquare.sg39182`, `OAI.UniversalTensorSquare.sg40054`, `OAI.UniversalTensorSquare.sg40784`, `OAI.UniversalTensorSquare.sg41579`, `OAI.UniversalTensorSquare.sg41659`, `OAI.UniversalTensorSquare.sg42167`, `OAI.UniversalTensorSquare.sg42272`, `OAI.UniversalTensorSquare.sg42670`, `OAI.UniversalTensorSquare.sg42866`, `OAI.UniversalTensorSquare.sg43021` and `OAI.UniversalTensorSquare.sg43088` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg65)

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

lemma sg65 : RowSquare [2,2,2] [6] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
