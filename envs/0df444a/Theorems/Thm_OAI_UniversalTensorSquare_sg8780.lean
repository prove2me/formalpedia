-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8780
-- name    : OAI.UniversalTensorSquare.sg8780
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:49:32.687003+00:00
-- url     : https://prove2.me/theorems/17a24797-ec4b-480c-b4ba-4178d8dfebea
-- title:
--   OAI.UniversalTensorSquare.sg8780: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8780` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8780 : RowSquare [6,6,3,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_109All`, `OAI.UniversalTensorSquare.degreeTree43_177All`, `OAI.UniversalTensorSquare.degreeTree43_207All`, `OAI.UniversalTensorSquare.degreeTree43_244All`, `OAI.UniversalTensorSquare.degreeTree43_258All`, `OAI.UniversalTensorSquare.degreeTree43_259All`, `OAI.UniversalTensorSquare.degreeTree43_269All`, `OAI.UniversalTensorSquare.degreeTree43_327All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_343All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_362All`, `OAI.UniversalTensorSquare.degreeTree43_377All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_428All`, `OAI.UniversalTensorSquare.degreeTree43_431All`, `OAI.UniversalTensorSquare.degreeTree43_435All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_484All`, `OAI.UniversalTensorSquare.degreeTree43_492All`, `OAI.UniversalTensorSquare.degreeTree43_497All`, `OAI.UniversalTensorSquare.degreeTree43_507All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_553All`, `OAI.UniversalTensorSquare.degreeTree43_572All`, `OAI.UniversalTensorSquare.degreeTree43_640All`, `OAI.UniversalTensorSquare.degreeTree43_642All`, `OAI.UniversalTensorSquare.sg17146`, `OAI.UniversalTensorSquare.sg23543`, `OAI.UniversalTensorSquare.sg23552`, `OAI.UniversalTensorSquare.sg24752`, `OAI.UniversalTensorSquare.sg24761`, `OAI.UniversalTensorSquare.sg26550`, `OAI.UniversalTensorSquare.sg27031`, `OAI.UniversalTensorSquare.sg27149`, `OAI.UniversalTensorSquare.sg27316`, `OAI.UniversalTensorSquare.sg27800`, `OAI.UniversalTensorSquare.sg27845`, `OAI.UniversalTensorSquare.sg27991`, `OAI.UniversalTensorSquare.sg28037`, `OAI.UniversalTensorSquare.sg28078`, `OAI.UniversalTensorSquare.sg28143`, `OAI.UniversalTensorSquare.sg28152`, `OAI.UniversalTensorSquare.sg28203`, `OAI.UniversalTensorSquare.sg28435`, `OAI.UniversalTensorSquare.sg28481`, `OAI.UniversalTensorSquare.sg28490`, `OAI.UniversalTensorSquare.sg28499`, `OAI.UniversalTensorSquare.sg28533`, `OAI.UniversalTensorSquare.sg28541`, `OAI.UniversalTensorSquare.sg28636`, `OAI.UniversalTensorSquare.sg28644`, `OAI.UniversalTensorSquare.sg28675`, `OAI.UniversalTensorSquare.sg28756`, `OAI.UniversalTensorSquare.sg28872`, `OAI.UniversalTensorSquare.sg28908`, `OAI.UniversalTensorSquare.sg29160`, `OAI.UniversalTensorSquare.sg29169`, `OAI.UniversalTensorSquare.sg29213`, `OAI.UniversalTensorSquare.sg29221`, `OAI.UniversalTensorSquare.sg29344`, `OAI.UniversalTensorSquare.sg29380`, `OAI.UniversalTensorSquare.sg29545`, `OAI.UniversalTensorSquare.sg29974`, `OAI.UniversalTensorSquare.sg29982`, `OAI.UniversalTensorSquare.sg30023`, `OAI.UniversalTensorSquare.sg30059`, `OAI.UniversalTensorSquare.sg30295`, `OAI.UniversalTensorSquare.sg30721`, `OAI.UniversalTensorSquare.sg30768`, `OAI.UniversalTensorSquare.sg30859`, `OAI.UniversalTensorSquare.sg31124`, `OAI.UniversalTensorSquare.sg31167` and `OAI.UniversalTensorSquare.sg31247` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg8780)

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

lemma sg8780 : RowSquare [6,6,3,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
