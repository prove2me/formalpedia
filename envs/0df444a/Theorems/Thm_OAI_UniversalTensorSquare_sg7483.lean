-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg7483
-- name    : OAI.UniversalTensorSquare.sg7483
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:36:42.27759+00:00
-- url     : https://prove2.me/theorems/6c92cc35-a09f-4afa-9f0e-cbddd3467b5b
-- title:
--   OAI.UniversalTensorSquare.sg7483: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg7483` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes17.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes17.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg7483 : RowSquare [6,4,3,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_100All`, `OAI.UniversalTensorSquare.degreeTree39_51All`, `OAI.UniversalTensorSquare.degreeTree39_54All`, `OAI.UniversalTensorSquare.degreeTree39_55All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_57All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_66All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_73All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree39_80All`, `OAI.UniversalTensorSquare.degreeTree39_81All`, `OAI.UniversalTensorSquare.degreeTree39_83All`, `OAI.UniversalTensorSquare.degreeTree39_86All`, `OAI.UniversalTensorSquare.degreeTree39_87All`, `OAI.UniversalTensorSquare.sg22486`, `OAI.UniversalTensorSquare.sg22493`, `OAI.UniversalTensorSquare.sg22527`, `OAI.UniversalTensorSquare.sg22553`, `OAI.UniversalTensorSquare.sg22639`, `OAI.UniversalTensorSquare.sg22672`, `OAI.UniversalTensorSquare.sg22730`, `OAI.UniversalTensorSquare.sg22768`, `OAI.UniversalTensorSquare.sg22803`, `OAI.UniversalTensorSquare.sg22909`, `OAI.UniversalTensorSquare.sg22922`, `OAI.UniversalTensorSquare.sg22940`, `OAI.UniversalTensorSquare.sg22976`, `OAI.UniversalTensorSquare.sg23024`, `OAI.UniversalTensorSquare.sg23032`, `OAI.UniversalTensorSquare.sg23038`, `OAI.UniversalTensorSquare.sg23057`, `OAI.UniversalTensorSquare.sg23238`, `OAI.UniversalTensorSquare.sg23245`, `OAI.UniversalTensorSquare.sg23252`, `OAI.UniversalTensorSquare.sg23259`, `OAI.UniversalTensorSquare.sg23281`, `OAI.UniversalTensorSquare.sg23289`, `OAI.UniversalTensorSquare.sg23295` and `OAI.UniversalTensorSquare.sg23314` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes17.lean (declaration OAI.UniversalTensorSquare.sg7483)

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

lemma sg7483 : RowSquare [6,4,3,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
