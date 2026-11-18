-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg590
-- name    : OAI.UniversalTensorSquare.sg590
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:46:29.69581+00:00
-- url     : https://prove2.me/theorems/722216ba-74b0-4854-a642-462684e490c6
-- title:
--   OAI.UniversalTensorSquare.sg590: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg590` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_37All`, `OAI.UniversalTensorSquare.degreeTree41_0All`, `OAI.UniversalTensorSquare.degreeTree43_305All`, `OAI.UniversalTensorSquare.degreeTree43_324All`, `OAI.UniversalTensorSquare.degreeTree43_368All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_489All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.degreeTree62_253All`, `OAI.UniversalTensorSquare.sg2297`, `OAI.UniversalTensorSquare.sg24429`, `OAI.UniversalTensorSquare.sg24718`, `OAI.UniversalTensorSquare.sg25001`, `OAI.UniversalTensorSquare.sg25065`, `OAI.UniversalTensorSquare.sg25281`, `OAI.UniversalTensorSquare.sg25326`, `OAI.UniversalTensorSquare.sg25358`, `OAI.UniversalTensorSquare.sg34401`, `OAI.UniversalTensorSquare.sg34515`, `OAI.UniversalTensorSquare.sg34516`, `OAI.UniversalTensorSquare.sg34517`, `OAI.UniversalTensorSquare.sg34533`, `OAI.UniversalTensorSquare.sg34537`, `OAI.UniversalTensorSquare.sg35033`, `OAI.UniversalTensorSquare.sg35186`, `OAI.UniversalTensorSquare.sg35194`, `OAI.UniversalTensorSquare.sg37330`, `OAI.UniversalTensorSquare.sg37332`, `OAI.UniversalTensorSquare.sg38215`, `OAI.UniversalTensorSquare.sg38217`, `OAI.UniversalTensorSquare.sg38797`, `OAI.UniversalTensorSquare.sg38798`, `OAI.UniversalTensorSquare.sg38800`, `OAI.UniversalTensorSquare.sg38801`, `OAI.UniversalTensorSquare.sg38803`, `OAI.UniversalTensorSquare.sg39413`, `OAI.UniversalTensorSquare.sg41777`, `OAI.UniversalTensorSquare.sg42057`, `OAI.UniversalTensorSquare.sg42750`, `OAI.UniversalTensorSquare.sg43005`, `OAI.UniversalTensorSquare.sg6942`, `OAI.UniversalTensorSquare.sg7099`, `OAI.UniversalTensorSquare.sg7155`, `OAI.UniversalTensorSquare.sg9000`, `OAI.UniversalTensorSquare.sg9195`, `OAI.UniversalTensorSquare.sg9801` and `OAI.UniversalTensorSquare.sg9830` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg590)

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

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
