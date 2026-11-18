-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg561
-- name    : OAI.UniversalTensorSquare.sg561
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:43:49.662989+00:00
-- url     : https://prove2.me/theorems/c7263a65-f3c5-4f6b-a98e-b08ced147f2e
-- title:
--   OAI.UniversalTensorSquare.sg561: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg561` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg561 : RowSquare [4,3,1,1] [2,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_20All`, `OAI.UniversalTensorSquare.degreeTree43_336All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_42All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degree_pos14`, `OAI.UniversalTensorSquare.sg11926`, `OAI.UniversalTensorSquare.sg11967`, `OAI.UniversalTensorSquare.sg12127`, `OAI.UniversalTensorSquare.sg13048`, `OAI.UniversalTensorSquare.sg13155`, `OAI.UniversalTensorSquare.sg13257`, `OAI.UniversalTensorSquare.sg13267`, `OAI.UniversalTensorSquare.sg13290`, `OAI.UniversalTensorSquare.sg28056`, `OAI.UniversalTensorSquare.sg28206`, `OAI.UniversalTensorSquare.sg28574`, `OAI.UniversalTensorSquare.sg29179`, `OAI.UniversalTensorSquare.sg29985`, `OAI.UniversalTensorSquare.sg29993`, `OAI.UniversalTensorSquare.sg30035`, `OAI.UniversalTensorSquare.sg30714`, `OAI.UniversalTensorSquare.sg3860` and `OAI.UniversalTensorSquare.sg42785` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg561)

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

lemma sg561 : RowSquare [4,3,1,1] [2,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
