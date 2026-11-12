-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg12954
-- name    : OAI.UniversalTensorSquare.sg12954
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:57:59.454205+00:00
-- url     : https://prove2.me/theorems/6f910469-7585-4996-897c-178cf566e4cd
-- title:
--   OAI.UniversalTensorSquare.sg12954: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg12954` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes31.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes31.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg12954 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_124All`, `OAI.UniversalTensorSquare.degreeTree43_263All`, `OAI.UniversalTensorSquare.degreeTree43_361All`, `OAI.UniversalTensorSquare.degreeTree43_434All`, `OAI.UniversalTensorSquare.degreeTree43_438All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_498All`, `OAI.UniversalTensorSquare.degreeTree43_582All`, `OAI.UniversalTensorSquare.degreeTree43_84All`, `OAI.UniversalTensorSquare.sg15653`, `OAI.UniversalTensorSquare.sg25914`, `OAI.UniversalTensorSquare.sg26307`, `OAI.UniversalTensorSquare.sg26996`, `OAI.UniversalTensorSquare.sg27146`, `OAI.UniversalTensorSquare.sg28650`, `OAI.UniversalTensorSquare.sg28681`, `OAI.UniversalTensorSquare.sg28878`, `OAI.UniversalTensorSquare.sg29182`, `OAI.UniversalTensorSquare.sg29542`, `OAI.UniversalTensorSquare.sg29988`, `OAI.UniversalTensorSquare.sg30136`, `OAI.UniversalTensorSquare.sg30727` and `OAI.UniversalTensorSquare.sg30765` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes31.lean (declaration OAI.UniversalTensorSquare.sg12954)

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

lemma sg12954 : RowSquare [8,7,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
