-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8648
-- name    : OAI.UniversalTensorSquare.sg8648
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:45:17.692377+00:00
-- url     : https://prove2.me/theorems/b23efa67-312f-4f27-bf13-908f620a1f2f
-- title:
--   OAI.UniversalTensorSquare.sg8648: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8648` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8648 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_144All`, `OAI.UniversalTensorSquare.degreeTree43_163All`, `OAI.UniversalTensorSquare.degreeTree43_201All`, `OAI.UniversalTensorSquare.degreeTree43_205All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_234All`, `OAI.UniversalTensorSquare.degreeTree43_253All`, `OAI.UniversalTensorSquare.degreeTree43_31All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_368All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_3All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_446All`, `OAI.UniversalTensorSquare.degreeTree43_44All`, `OAI.UniversalTensorSquare.degreeTree43_461All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_480All`, `OAI.UniversalTensorSquare.degreeTree43_485All`, `OAI.UniversalTensorSquare.degreeTree43_486All`, `OAI.UniversalTensorSquare.degreeTree43_489All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_51All`, `OAI.UniversalTensorSquare.degreeTree43_580All`, `OAI.UniversalTensorSquare.degreeTree43_583All`, `OAI.UniversalTensorSquare.degreeTree43_5All`, `OAI.UniversalTensorSquare.degreeTree43_80All`, `OAI.UniversalTensorSquare.sg23710`, `OAI.UniversalTensorSquare.sg23712`, `OAI.UniversalTensorSquare.sg23719`, `OAI.UniversalTensorSquare.sg23722`, `OAI.UniversalTensorSquare.sg23822`, `OAI.UniversalTensorSquare.sg24017`, `OAI.UniversalTensorSquare.sg24032`, `OAI.UniversalTensorSquare.sg24115`, `OAI.UniversalTensorSquare.sg24166`, `OAI.UniversalTensorSquare.sg24236`, `OAI.UniversalTensorSquare.sg25456`, `OAI.UniversalTensorSquare.sg25486`, `OAI.UniversalTensorSquare.sg25498`, `OAI.UniversalTensorSquare.sg25547`, `OAI.UniversalTensorSquare.sg25614`, `OAI.UniversalTensorSquare.sg25638`, `OAI.UniversalTensorSquare.sg25771`, `OAI.UniversalTensorSquare.sg26260`, `OAI.UniversalTensorSquare.sg26511`, `OAI.UniversalTensorSquare.sg28710`, `OAI.UniversalTensorSquare.sg28808`, `OAI.UniversalTensorSquare.sg29324`, `OAI.UniversalTensorSquare.sg29432`, `OAI.UniversalTensorSquare.sg29477`, `OAI.UniversalTensorSquare.sg30058`, `OAI.UniversalTensorSquare.sg30200`, `OAI.UniversalTensorSquare.sg30829` and `OAI.UniversalTensorSquare.sg30970` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean (declaration OAI.UniversalTensorSquare.sg8648)

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

lemma sg8648 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
