-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg14319
-- name    : OAI.UniversalTensorSquare.sg14319
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:06:35.36196+00:00
-- url     : https://prove2.me/theorems/9c65618f-5d3a-47ad-9163-621cd75698de
-- title:
--   OAI.UniversalTensorSquare.sg14319: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg14319` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes34.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes34.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg14319 : RowSquare [6,4,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_273All`, `OAI.UniversalTensorSquare.degreeTree62_285All`, `OAI.UniversalTensorSquare.sg19620`, `OAI.UniversalTensorSquare.sg34348`, `OAI.UniversalTensorSquare.sg34435`, `OAI.UniversalTensorSquare.sg34518`, `OAI.UniversalTensorSquare.sg34527`, `OAI.UniversalTensorSquare.sg34573`, `OAI.UniversalTensorSquare.sg34589`, `OAI.UniversalTensorSquare.sg35016`, `OAI.UniversalTensorSquare.sg35055`, `OAI.UniversalTensorSquare.sg35081`, `OAI.UniversalTensorSquare.sg35180`, `OAI.UniversalTensorSquare.sg35201`, `OAI.UniversalTensorSquare.sg35206`, `OAI.UniversalTensorSquare.sg35226`, `OAI.UniversalTensorSquare.sg35242`, `OAI.UniversalTensorSquare.sg35316`, `OAI.UniversalTensorSquare.sg35321` and `OAI.UniversalTensorSquare.sg35428` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes34.lean (declaration OAI.UniversalTensorSquare.sg14319)

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

lemma sg14319 : RowSquare [6,4,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
