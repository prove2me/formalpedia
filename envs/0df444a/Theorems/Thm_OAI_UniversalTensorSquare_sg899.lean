-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg899
-- name    : OAI.UniversalTensorSquare.sg899
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:56:17.863841+00:00
-- url     : https://prove2.me/theorems/5a781913-3f90-4505-80cc-0f6a1408f5dc
-- title:
--   OAI.UniversalTensorSquare.sg899: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg899` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg899 : RowSquare [5,1,1,1,1,1] [3,3,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_60All`, `OAI.UniversalTensorSquare.degreeTree43_221All`, `OAI.UniversalTensorSquare.sg10401`, `OAI.UniversalTensorSquare.sg1349`, `OAI.UniversalTensorSquare.sg24690`, `OAI.UniversalTensorSquare.sg34289`, `OAI.UniversalTensorSquare.sg34290`, `OAI.UniversalTensorSquare.sg34292`, `OAI.UniversalTensorSquare.sg34293`, `OAI.UniversalTensorSquare.sg34295`, `OAI.UniversalTensorSquare.sg34297`, `OAI.UniversalTensorSquare.sg34310`, `OAI.UniversalTensorSquare.sg34311`, `OAI.UniversalTensorSquare.sg34313`, `OAI.UniversalTensorSquare.sg34314`, `OAI.UniversalTensorSquare.sg34316`, `OAI.UniversalTensorSquare.sg34318`, `OAI.UniversalTensorSquare.sg7355`, `OAI.UniversalTensorSquare.sg7358`, `OAI.UniversalTensorSquare.sg7359`, `OAI.UniversalTensorSquare.sg7580`, `OAI.UniversalTensorSquare.sg7587`, `OAI.UniversalTensorSquare.sg7590`, `OAI.UniversalTensorSquare.sg7591`, `OAI.UniversalTensorSquare.sg7657` and `OAI.UniversalTensorSquare.sg7658` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg899)

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

lemma sg899 : RowSquare [5,1,1,1,1,1] [3,3,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
