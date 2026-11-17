-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2633
-- name    : OAI.UniversalTensorSquare.sg2633
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T10:11:06.117863+00:00
-- url     : https://prove2.me/theorems/5e7f07ef-21a2-4cf5-ad7d-575d2468bf1b
-- title:
--   OAI.UniversalTensorSquare.sg2633: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2633` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2633 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_11All`, `OAI.UniversalTensorSquare.degreeTree62_155All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_29All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_32All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_47All`, `OAI.UniversalTensorSquare.degreeTree62_56All`, `OAI.UniversalTensorSquare.degreeTree62_59All`, `OAI.UniversalTensorSquare.degreeTree62_620All`, `OAI.UniversalTensorSquare.degreeTree62_67All`, `OAI.UniversalTensorSquare.degreeTree62_714All`, `OAI.UniversalTensorSquare.degreeTree62_717All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_94All`, `OAI.UniversalTensorSquare.sg11736`, `OAI.UniversalTensorSquare.sg14762`, `OAI.UniversalTensorSquare.sg17188`, `OAI.UniversalTensorSquare.sg19290`, `OAI.UniversalTensorSquare.sg23972`, `OAI.UniversalTensorSquare.sg24069`, `OAI.UniversalTensorSquare.sg24070`, `OAI.UniversalTensorSquare.sg24139`, `OAI.UniversalTensorSquare.sg24140`, `OAI.UniversalTensorSquare.sg24188`, `OAI.UniversalTensorSquare.sg24207`, `OAI.UniversalTensorSquare.sg24217`, `OAI.UniversalTensorSquare.sg24292`, `OAI.UniversalTensorSquare.sg24573`, `OAI.UniversalTensorSquare.sg24576`, `OAI.UniversalTensorSquare.sg24646`, `OAI.UniversalTensorSquare.sg25522`, `OAI.UniversalTensorSquare.sg25589`, `OAI.UniversalTensorSquare.sg25744`, `OAI.UniversalTensorSquare.sg32601`, `OAI.UniversalTensorSquare.sg33121`, `OAI.UniversalTensorSquare.sg35427`, `OAI.UniversalTensorSquare.sg36276` and `OAI.UniversalTensorSquare.sg36395` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2633)

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

lemma sg2633 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
