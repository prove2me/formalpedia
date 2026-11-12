-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1378
-- name    : OAI.UniversalTensorSquare.sg1378
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:15:39.048897+00:00
-- url     : https://prove2.me/theorems/92b35de5-1ef4-437a-9273-d90180d3c3a4
-- title:
--   OAI.UniversalTensorSquare.sg1378: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1378` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1378 : RowSquare [6,2,1,1,1] [3,3,3,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_123All`, `OAI.UniversalTensorSquare.degreeTree43_126All`, `OAI.UniversalTensorSquare.degreeTree43_15All`, `OAI.UniversalTensorSquare.degreeTree43_163All`, `OAI.UniversalTensorSquare.degreeTree43_177All`, `OAI.UniversalTensorSquare.degreeTree43_181All`, `OAI.UniversalTensorSquare.degreeTree43_289All`, `OAI.UniversalTensorSquare.degreeTree43_290All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_38All`, `OAI.UniversalTensorSquare.degreeTree43_536All`, `OAI.UniversalTensorSquare.degreeTree43_546All`, `OAI.UniversalTensorSquare.degreeTree43_550All`, `OAI.UniversalTensorSquare.degreeTree43_89All`, `OAI.UniversalTensorSquare.sg22778`, `OAI.UniversalTensorSquare.sg24270`, `OAI.UniversalTensorSquare.sg24586`, `OAI.UniversalTensorSquare.sg24889`, `OAI.UniversalTensorSquare.sg24919`, `OAI.UniversalTensorSquare.sg24920`, `OAI.UniversalTensorSquare.sg25103`, `OAI.UniversalTensorSquare.sg25147`, `OAI.UniversalTensorSquare.sg25154`, `OAI.UniversalTensorSquare.sg25182`, `OAI.UniversalTensorSquare.sg25183`, `OAI.UniversalTensorSquare.sg25197`, `OAI.UniversalTensorSquare.sg25218`, `OAI.UniversalTensorSquare.sg25223`, `OAI.UniversalTensorSquare.sg26389`, `OAI.UniversalTensorSquare.sg26669`, `OAI.UniversalTensorSquare.sg26671`, `OAI.UniversalTensorSquare.sg26800`, `OAI.UniversalTensorSquare.sg27524`, `OAI.UniversalTensorSquare.sg30651`, `OAI.UniversalTensorSquare.sg30666`, `OAI.UniversalTensorSquare.sg31361`, `OAI.UniversalTensorSquare.sg31388`, `OAI.UniversalTensorSquare.sg34720`, `OAI.UniversalTensorSquare.sg6821`, `OAI.UniversalTensorSquare.sg7069`, `OAI.UniversalTensorSquare.sg7096`, `OAI.UniversalTensorSquare.sg9753` and `OAI.UniversalTensorSquare.sg9756` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1378)

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

lemma sg1378 : RowSquare [6,2,1,1,1] [3,3,3,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
