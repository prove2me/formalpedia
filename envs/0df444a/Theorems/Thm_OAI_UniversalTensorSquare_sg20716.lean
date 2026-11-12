-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20716
-- name    : OAI.UniversalTensorSquare.sg20716
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:55:59.015063+00:00
-- url     : https://prove2.me/theorems/00c7490f-3e91-4d22-a923-aca4bd8b0fb9
-- title:
--   OAI.UniversalTensorSquare.sg20716: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20716` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20716 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,3,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_104All`, `OAI.UniversalTensorSquare.degreeTree62_127All`, `OAI.UniversalTensorSquare.degreeTree62_435All`, `OAI.UniversalTensorSquare.degreeTree62_478All`, `OAI.UniversalTensorSquare.degreeTree62_494All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_81All`, `OAI.UniversalTensorSquare.sg32734`, `OAI.UniversalTensorSquare.sg33094`, `OAI.UniversalTensorSquare.sg33186`, `OAI.UniversalTensorSquare.sg37315`, `OAI.UniversalTensorSquare.sg37506`, `OAI.UniversalTensorSquare.sg37509`, `OAI.UniversalTensorSquare.sg38191`, `OAI.UniversalTensorSquare.sg38200`, `OAI.UniversalTensorSquare.sg38602`, `OAI.UniversalTensorSquare.sg38607`, `OAI.UniversalTensorSquare.sg38763`, `OAI.UniversalTensorSquare.sg38766`, `OAI.UniversalTensorSquare.sg39380`, `OAI.UniversalTensorSquare.sg39385`, `OAI.UniversalTensorSquare.sg39630`, `OAI.UniversalTensorSquare.sg39741`, `OAI.UniversalTensorSquare.sg39749`, `OAI.UniversalTensorSquare.sg39869` and `OAI.UniversalTensorSquare.sg39872` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean (declaration OAI.UniversalTensorSquare.sg20716)

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

lemma sg20716 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,3,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
