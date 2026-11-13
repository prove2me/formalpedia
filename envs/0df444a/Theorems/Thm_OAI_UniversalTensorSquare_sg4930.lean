-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4930
-- name    : OAI.UniversalTensorSquare.sg4930
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:18:39.98714+00:00
-- url     : https://prove2.me/theorems/e9e79148-689e-4cf2-bb59-9a8d16a960fb
-- title:
--   OAI.UniversalTensorSquare.sg4930: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4930` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4930 : RowSquare [9,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_168All`, `OAI.UniversalTensorSquare.degreeTree43_220All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_249All`, `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.degreeTree43_295All`, `OAI.UniversalTensorSquare.degreeTree43_400All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_451All`, `OAI.UniversalTensorSquare.degreeTree43_461All`, `OAI.UniversalTensorSquare.degreeTree43_468All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_513All`, `OAI.UniversalTensorSquare.degreeTree43_521All`, `OAI.UniversalTensorSquare.degreeTree43_558All`, `OAI.UniversalTensorSquare.degreeTree43_580All`, `OAI.UniversalTensorSquare.degreeTree43_596All`, `OAI.UniversalTensorSquare.degreeTree43_616All`, `OAI.UniversalTensorSquare.degreeTree43_627All`, `OAI.UniversalTensorSquare.degreeTree43_630All`, `OAI.UniversalTensorSquare.degreeTree43_631All`, `OAI.UniversalTensorSquare.degreeTree43_642All`, `OAI.UniversalTensorSquare.sg26373`, `OAI.UniversalTensorSquare.sg26414`, `OAI.UniversalTensorSquare.sg26597`, `OAI.UniversalTensorSquare.sg26643`, `OAI.UniversalTensorSquare.sg26795`, `OAI.UniversalTensorSquare.sg26815`, `OAI.UniversalTensorSquare.sg27363`, `OAI.UniversalTensorSquare.sg27407`, `OAI.UniversalTensorSquare.sg28942`, `OAI.UniversalTensorSquare.sg28987`, `OAI.UniversalTensorSquare.sg29007`, `OAI.UniversalTensorSquare.sg29459`, `OAI.UniversalTensorSquare.sg29588`, `OAI.UniversalTensorSquare.sg29639`, `OAI.UniversalTensorSquare.sg29704`, `OAI.UniversalTensorSquare.sg29778`, `OAI.UniversalTensorSquare.sg29800`, `OAI.UniversalTensorSquare.sg29847`, `OAI.UniversalTensorSquare.sg30093`, `OAI.UniversalTensorSquare.sg30202`, `OAI.UniversalTensorSquare.sg30473`, `OAI.UniversalTensorSquare.sg30601`, `OAI.UniversalTensorSquare.sg30608`, `OAI.UniversalTensorSquare.sg30630`, `OAI.UniversalTensorSquare.sg30811`, `OAI.UniversalTensorSquare.sg30878`, `OAI.UniversalTensorSquare.sg30900`, `OAI.UniversalTensorSquare.sg30906`, `OAI.UniversalTensorSquare.sg30944`, `OAI.UniversalTensorSquare.sg30998`, `OAI.UniversalTensorSquare.sg31004`, `OAI.UniversalTensorSquare.sg31023`, `OAI.UniversalTensorSquare.sg31207`, `OAI.UniversalTensorSquare.sg31213`, `OAI.UniversalTensorSquare.sg31259`, `OAI.UniversalTensorSquare.sg31265`, `OAI.UniversalTensorSquare.sg31283`, `OAI.UniversalTensorSquare.sg31345`, `OAI.UniversalTensorSquare.sg31352`, `OAI.UniversalTensorSquare.sg31372`, `OAI.UniversalTensorSquare.sg31515` and `OAI.UniversalTensorSquare.sg31728` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg4930)

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

lemma sg4930 : RowSquare [9,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
