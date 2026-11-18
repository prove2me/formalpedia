-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8415
-- name    : OAI.UniversalTensorSquare.sg8415
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:39:16.827297+00:00
-- url     : https://prove2.me/theorems/16064e3c-ee60-4498-a755-5401baaa6012
-- title:
--   OAI.UniversalTensorSquare.sg8415: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8415` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8415 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_164All`, `OAI.UniversalTensorSquare.degreeTree43_165All`, `OAI.UniversalTensorSquare.degreeTree43_198All`, `OAI.UniversalTensorSquare.degreeTree43_205All`, `OAI.UniversalTensorSquare.degreeTree43_24All`, `OAI.UniversalTensorSquare.degreeTree43_275All`, `OAI.UniversalTensorSquare.degreeTree43_27All`, `OAI.UniversalTensorSquare.degreeTree43_28All`, `OAI.UniversalTensorSquare.degreeTree43_292All`, `OAI.UniversalTensorSquare.degreeTree43_31All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_35All`, `OAI.UniversalTensorSquare.degreeTree43_589All`, `OAI.UniversalTensorSquare.degreeTree43_595All`, `OAI.UniversalTensorSquare.degreeTree43_70All`, `OAI.UniversalTensorSquare.sg23709`, `OAI.UniversalTensorSquare.sg23718`, `OAI.UniversalTensorSquare.sg23777`, `OAI.UniversalTensorSquare.sg23854`, `OAI.UniversalTensorSquare.sg23959`, `OAI.UniversalTensorSquare.sg24490`, `OAI.UniversalTensorSquare.sg25390`, `OAI.UniversalTensorSquare.sg25452`, `OAI.UniversalTensorSquare.sg25466`, `OAI.UniversalTensorSquare.sg25469`, `OAI.UniversalTensorSquare.sg25480`, `OAI.UniversalTensorSquare.sg25496`, `OAI.UniversalTensorSquare.sg25533`, `OAI.UniversalTensorSquare.sg25565`, `OAI.UniversalTensorSquare.sg25612`, `OAI.UniversalTensorSquare.sg25753`, `OAI.UniversalTensorSquare.sg28134`, `OAI.UniversalTensorSquare.sg28279`, `OAI.UniversalTensorSquare.sg28384`, `OAI.UniversalTensorSquare.sg28611`, `OAI.UniversalTensorSquare.sg28617`, `OAI.UniversalTensorSquare.sg28732`, `OAI.UniversalTensorSquare.sg28744`, `OAI.UniversalTensorSquare.sg28786`, `OAI.UniversalTensorSquare.sg28836`, `OAI.UniversalTensorSquare.sg28957`, `OAI.UniversalTensorSquare.sg29041`, `OAI.UniversalTensorSquare.sg29093`, `OAI.UniversalTensorSquare.sg29309`, `OAI.UniversalTensorSquare.sg29321`, `OAI.UniversalTensorSquare.sg29410`, `OAI.UniversalTensorSquare.sg29429`, `OAI.UniversalTensorSquare.sg29438`, `OAI.UniversalTensorSquare.sg29513`, `OAI.UniversalTensorSquare.sg29668`, `OAI.UniversalTensorSquare.sg29716`, `OAI.UniversalTensorSquare.sg29901`, `OAI.UniversalTensorSquare.sg30117`, `OAI.UniversalTensorSquare.sg30365`, `OAI.UniversalTensorSquare.sg30929` and `OAI.UniversalTensorSquare.sg31577` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8415)

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

lemma sg8415 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
