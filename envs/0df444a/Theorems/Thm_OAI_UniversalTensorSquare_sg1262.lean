-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1262
-- name    : OAI.UniversalTensorSquare.sg1262
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:57:21.632522+00:00
-- url     : https://prove2.me/theorems/85408d4e-0d51-4ea1-baac-6f1895dd38ae
-- title:
--   OAI.UniversalTensorSquare.sg1262: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1262` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1262 : RowSquare [5,2,1,1,1,1] [3,3,3,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_305All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.sg24587`, `OAI.UniversalTensorSquare.sg24917`, `OAI.UniversalTensorSquare.sg24923`, `OAI.UniversalTensorSquare.sg25185`, `OAI.UniversalTensorSquare.sg25207`, `OAI.UniversalTensorSquare.sg25227`, `OAI.UniversalTensorSquare.sg25264`, `OAI.UniversalTensorSquare.sg25275`, `OAI.UniversalTensorSquare.sg25278`, `OAI.UniversalTensorSquare.sg25284`, `OAI.UniversalTensorSquare.sg25286`, `OAI.UniversalTensorSquare.sg34633`, `OAI.UniversalTensorSquare.sg34635` and `OAI.UniversalTensorSquare.sg34756` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1262)

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

lemma sg1262 : RowSquare [5,2,1,1,1,1] [3,3,3,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
