-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1756
-- name    : OAI.UniversalTensorSquare.sg1756
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:34:06.505688+00:00
-- url     : https://prove2.me/theorems/f11b5108-8e10-4309-b57d-73a95b910d28
-- title:
--   OAI.UniversalTensorSquare.sg1756: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1756` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1756 : RowSquare [6,2,1,1,1,1] [2,2,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_113All`, `OAI.UniversalTensorSquare.degreeTree43_126All`, `OAI.UniversalTensorSquare.degreeTree62_183All`, `OAI.UniversalTensorSquare.degreeTree62_232All`, `OAI.UniversalTensorSquare.degreeTree62_233All`, `OAI.UniversalTensorSquare.degreeTree62_236All`, `OAI.UniversalTensorSquare.degreeTree62_238All`, `OAI.UniversalTensorSquare.degreeTree62_239All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_253All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_262All`, `OAI.UniversalTensorSquare.degreeTree62_420All`, `OAI.UniversalTensorSquare.degreeTree62_422All`, `OAI.UniversalTensorSquare.degreeTree62_461All`, `OAI.UniversalTensorSquare.degreeTree62_522All`, `OAI.UniversalTensorSquare.degreeTree62_630All`, `OAI.UniversalTensorSquare.degreeTree62_650All`, `OAI.UniversalTensorSquare.sg11278`, `OAI.UniversalTensorSquare.sg11280`, `OAI.UniversalTensorSquare.sg11304`, `OAI.UniversalTensorSquare.sg11307`, `OAI.UniversalTensorSquare.sg22040`, `OAI.UniversalTensorSquare.sg22042`, `OAI.UniversalTensorSquare.sg22046`, `OAI.UniversalTensorSquare.sg24227`, `OAI.UniversalTensorSquare.sg24596`, `OAI.UniversalTensorSquare.sg24627`, `OAI.UniversalTensorSquare.sg24790`, `OAI.UniversalTensorSquare.sg24818`, `OAI.UniversalTensorSquare.sg24821`, `OAI.UniversalTensorSquare.sg24846`, `OAI.UniversalTensorSquare.sg24898`, `OAI.UniversalTensorSquare.sg24991`, `OAI.UniversalTensorSquare.sg25115`, `OAI.UniversalTensorSquare.sg25136`, `OAI.UniversalTensorSquare.sg25140`, `OAI.UniversalTensorSquare.sg25149`, `OAI.UniversalTensorSquare.sg25154`, `OAI.UniversalTensorSquare.sg25184`, `OAI.UniversalTensorSquare.sg25189`, `OAI.UniversalTensorSquare.sg25200`, `OAI.UniversalTensorSquare.sg25215`, `OAI.UniversalTensorSquare.sg25247`, `OAI.UniversalTensorSquare.sg25267`, `OAI.UniversalTensorSquare.sg25270`, `OAI.UniversalTensorSquare.sg25316`, `OAI.UniversalTensorSquare.sg27452`, `OAI.UniversalTensorSquare.sg27791`, `OAI.UniversalTensorSquare.sg28028`, `OAI.UniversalTensorSquare.sg28237`, `OAI.UniversalTensorSquare.sg28244`, `OAI.UniversalTensorSquare.sg34715`, `OAI.UniversalTensorSquare.sg34742`, `OAI.UniversalTensorSquare.sg34800`, `OAI.UniversalTensorSquare.sg34808`, `OAI.UniversalTensorSquare.sg34810`, `OAI.UniversalTensorSquare.sg34913`, `OAI.UniversalTensorSquare.sg34953`, `OAI.UniversalTensorSquare.sg34955`, `OAI.UniversalTensorSquare.sg34970`, `OAI.UniversalTensorSquare.sg34996`, `OAI.UniversalTensorSquare.sg35028`, `OAI.UniversalTensorSquare.sg35141`, `OAI.UniversalTensorSquare.sg35159`, `OAI.UniversalTensorSquare.sg36624`, `OAI.UniversalTensorSquare.sg36630`, `OAI.UniversalTensorSquare.sg37086`, `OAI.UniversalTensorSquare.sg38393`, `OAI.UniversalTensorSquare.sg39192`, `OAI.UniversalTensorSquare.sg39227`, `OAI.UniversalTensorSquare.sg42693`, `OAI.UniversalTensorSquare.sg7453`, `OAI.UniversalTensorSquare.sg8465`, `OAI.UniversalTensorSquare.sg8467` and `OAI.UniversalTensorSquare.sg9461` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean (declaration OAI.UniversalTensorSquare.sg1756)

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

lemma sg1756 : RowSquare [6,2,1,1,1,1] [2,2,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
