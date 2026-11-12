-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1379
-- name    : OAI.UniversalTensorSquare.sg1379
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:15:35.926807+00:00
-- url     : https://prove2.me/theorems/e4835858-4c9a-4505-b672-eb58eb2840b0
-- title:
--   OAI.UniversalTensorSquare.sg1379: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1379` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1379 : RowSquare [6,2,1,1,1] [3,3,3,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_126All`, `OAI.UniversalTensorSquare.degreeTree43_129All`, `OAI.UniversalTensorSquare.degreeTree43_15All`, `OAI.UniversalTensorSquare.degreeTree43_179All`, `OAI.UniversalTensorSquare.degreeTree43_190All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_38All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_538All`, `OAI.UniversalTensorSquare.degreeTree43_549All`, `OAI.UniversalTensorSquare.degreeTree43_550All`, `OAI.UniversalTensorSquare.sg22005`, `OAI.UniversalTensorSquare.sg22800`, `OAI.UniversalTensorSquare.sg24306`, `OAI.UniversalTensorSquare.sg24317`, `OAI.UniversalTensorSquare.sg24328`, `OAI.UniversalTensorSquare.sg24330`, `OAI.UniversalTensorSquare.sg24602`, `OAI.UniversalTensorSquare.sg24865`, `OAI.UniversalTensorSquare.sg24876`, `OAI.UniversalTensorSquare.sg24952`, `OAI.UniversalTensorSquare.sg24971`, `OAI.UniversalTensorSquare.sg24972`, `OAI.UniversalTensorSquare.sg25125`, `OAI.UniversalTensorSquare.sg25184`, `OAI.UniversalTensorSquare.sg25185`, `OAI.UniversalTensorSquare.sg25239`, `OAI.UniversalTensorSquare.sg25240`, `OAI.UniversalTensorSquare.sg25242`, `OAI.UniversalTensorSquare.sg25247`, `OAI.UniversalTensorSquare.sg25262`, `OAI.UniversalTensorSquare.sg25293`, `OAI.UniversalTensorSquare.sg25298`, `OAI.UniversalTensorSquare.sg25310`, `OAI.UniversalTensorSquare.sg25771`, `OAI.UniversalTensorSquare.sg26430`, `OAI.UniversalTensorSquare.sg26710`, `OAI.UniversalTensorSquare.sg26712`, `OAI.UniversalTensorSquare.sg26820`, `OAI.UniversalTensorSquare.sg30666`, `OAI.UniversalTensorSquare.sg30680`, `OAI.UniversalTensorSquare.sg31397`, `OAI.UniversalTensorSquare.sg6824`, `OAI.UniversalTensorSquare.sg7071`, `OAI.UniversalTensorSquare.sg7099`, `OAI.UniversalTensorSquare.sg7156`, `OAI.UniversalTensorSquare.sg9755` and `OAI.UniversalTensorSquare.sg9759` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1379)

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

lemma sg1379 : RowSquare [6,2,1,1,1] [3,3,3,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
