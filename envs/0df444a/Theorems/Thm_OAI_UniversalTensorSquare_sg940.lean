-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg940
-- name    : OAI.UniversalTensorSquare.sg940
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:02:07.135638+00:00
-- url     : https://prove2.me/theorems/a4b29caa-78a5-4cf8-b6a9-2a24d8eac6f5
-- title:
--   OAI.UniversalTensorSquare.sg940: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg940` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg940 : RowSquare [5,2,2,1] [2,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_32All`, `OAI.UniversalTensorSquare.degreeTree62_342All`, `OAI.UniversalTensorSquare.degreeTree62_654All`, `OAI.UniversalTensorSquare.degreeTree62_758All`, `OAI.UniversalTensorSquare.degreeTree62_878All`, `OAI.UniversalTensorSquare.degreeTree62_889All`, `OAI.UniversalTensorSquare.degreeTree62_917All`, `OAI.UniversalTensorSquare.sg1202`, `OAI.UniversalTensorSquare.sg12132`, `OAI.UniversalTensorSquare.sg12148`, `OAI.UniversalTensorSquare.sg13085`, `OAI.UniversalTensorSquare.sg13097`, `OAI.UniversalTensorSquare.sg14607`, `OAI.UniversalTensorSquare.sg1637`, `OAI.UniversalTensorSquare.sg26329`, `OAI.UniversalTensorSquare.sg26593`, `OAI.UniversalTensorSquare.sg36529`, `OAI.UniversalTensorSquare.sg37848`, `OAI.UniversalTensorSquare.sg37998`, `OAI.UniversalTensorSquare.sg38386`, `OAI.UniversalTensorSquare.sg38431`, `OAI.UniversalTensorSquare.sg38434`, `OAI.UniversalTensorSquare.sg38436`, `OAI.UniversalTensorSquare.sg39060`, `OAI.UniversalTensorSquare.sg39203`, `OAI.UniversalTensorSquare.sg39226`, `OAI.UniversalTensorSquare.sg39231`, `OAI.UniversalTensorSquare.sg39267`, `OAI.UniversalTensorSquare.sg39390`, `OAI.UniversalTensorSquare.sg39395`, `OAI.UniversalTensorSquare.sg39397`, `OAI.UniversalTensorSquare.sg39541`, `OAI.UniversalTensorSquare.sg39561`, `OAI.UniversalTensorSquare.sg39568`, `OAI.UniversalTensorSquare.sg39571`, `OAI.UniversalTensorSquare.sg39572`, `OAI.UniversalTensorSquare.sg40256`, `OAI.UniversalTensorSquare.sg40381`, `OAI.UniversalTensorSquare.sg40816`, `OAI.UniversalTensorSquare.sg40976`, `OAI.UniversalTensorSquare.sg40978`, `OAI.UniversalTensorSquare.sg40979`, `OAI.UniversalTensorSquare.sg41016`, `OAI.UniversalTensorSquare.sg41018`, `OAI.UniversalTensorSquare.sg41019`, `OAI.UniversalTensorSquare.sg41088`, `OAI.UniversalTensorSquare.sg41090`, `OAI.UniversalTensorSquare.sg41091`, `OAI.UniversalTensorSquare.sg41565`, `OAI.UniversalTensorSquare.sg41567`, `OAI.UniversalTensorSquare.sg41587`, `OAI.UniversalTensorSquare.sg41589`, `OAI.UniversalTensorSquare.sg41595`, `OAI.UniversalTensorSquare.sg41597`, `OAI.UniversalTensorSquare.sg41667`, `OAI.UniversalTensorSquare.sg41669`, `OAI.UniversalTensorSquare.sg41675`, `OAI.UniversalTensorSquare.sg41677`, `OAI.UniversalTensorSquare.sg41769`, `OAI.UniversalTensorSquare.sg41854`, `OAI.UniversalTensorSquare.sg41864`, `OAI.UniversalTensorSquare.sg41900`, `OAI.UniversalTensorSquare.sg42101`, `OAI.UniversalTensorSquare.sg42110`, `OAI.UniversalTensorSquare.sg42121`, `OAI.UniversalTensorSquare.sg42131`, `OAI.UniversalTensorSquare.sg42152`, `OAI.UniversalTensorSquare.sg42156`, `OAI.UniversalTensorSquare.sg42213`, `OAI.UniversalTensorSquare.sg42220`, `OAI.UniversalTensorSquare.sg42249`, `OAI.UniversalTensorSquare.sg6645`, `OAI.UniversalTensorSquare.sg6670`, `OAI.UniversalTensorSquare.sg9093` and `OAI.UniversalTensorSquare.sg9095` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg940)

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

lemma sg940 : RowSquare [5,2,2,1] [2,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
