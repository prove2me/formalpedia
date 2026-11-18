-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg537
-- name    : OAI.UniversalTensorSquare.sg537
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:41:16.941276+00:00
-- url     : https://prove2.me/theorems/114779c3-5bf9-4f0e-8d2a-17baa8a9edfe
-- title:
--   OAI.UniversalTensorSquare.sg537: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg537` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg537 : RowSquare [4,2,1,1,1] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_110All`, `OAI.UniversalTensorSquare.degreeTree39_19All`, `OAI.UniversalTensorSquare.degreeTree39_24All`, `OAI.UniversalTensorSquare.degreeTree41_0All`, `OAI.UniversalTensorSquare.degreeTree43_127All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_221All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_253All`, `OAI.UniversalTensorSquare.degreeTree43_256All`, `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree43_280All`, `OAI.UniversalTensorSquare.degreeTree43_292All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_306All`, `OAI.UniversalTensorSquare.degreeTree43_321All`, `OAI.UniversalTensorSquare.degreeTree43_366All`, `OAI.UniversalTensorSquare.degreeTree43_368All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_461All`, `OAI.UniversalTensorSquare.degreeTree43_480All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_618All`, `OAI.UniversalTensorSquare.degreeTree43_61All`, `OAI.UniversalTensorSquare.degreeTree43_645All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_620All`, `OAI.UniversalTensorSquare.sg21878`, `OAI.UniversalTensorSquare.sg21892`, `OAI.UniversalTensorSquare.sg21901`, `OAI.UniversalTensorSquare.sg21923`, `OAI.UniversalTensorSquare.sg22006`, `OAI.UniversalTensorSquare.sg22059`, `OAI.UniversalTensorSquare.sg22073`, `OAI.UniversalTensorSquare.sg22285`, `OAI.UniversalTensorSquare.sg22363`, `OAI.UniversalTensorSquare.sg22374`, `OAI.UniversalTensorSquare.sg22712`, `OAI.UniversalTensorSquare.sg22805`, `OAI.UniversalTensorSquare.sg22807`, `OAI.UniversalTensorSquare.sg22852`, `OAI.UniversalTensorSquare.sg22866`, `OAI.UniversalTensorSquare.sg22985`, `OAI.UniversalTensorSquare.sg23066`, `OAI.UniversalTensorSquare.sg23103`, `OAI.UniversalTensorSquare.sg23114`, `OAI.UniversalTensorSquare.sg24535`, `OAI.UniversalTensorSquare.sg24682`, `OAI.UniversalTensorSquare.sg24688`, `OAI.UniversalTensorSquare.sg24706`, `OAI.UniversalTensorSquare.sg24898`, `OAI.UniversalTensorSquare.sg24991`, `OAI.UniversalTensorSquare.sg24996`, `OAI.UniversalTensorSquare.sg25050`, `OAI.UniversalTensorSquare.sg25056`, `OAI.UniversalTensorSquare.sg25058`, `OAI.UniversalTensorSquare.sg25069`, `OAI.UniversalTensorSquare.sg25267`, `OAI.UniversalTensorSquare.sg25301`, `OAI.UniversalTensorSquare.sg25320`, `OAI.UniversalTensorSquare.sg26026`, `OAI.UniversalTensorSquare.sg26197`, `OAI.UniversalTensorSquare.sg26205`, `OAI.UniversalTensorSquare.sg27279`, `OAI.UniversalTensorSquare.sg27471`, `OAI.UniversalTensorSquare.sg27488`, `OAI.UniversalTensorSquare.sg27493`, `OAI.UniversalTensorSquare.sg30911`, `OAI.UniversalTensorSquare.sg31325`, `OAI.UniversalTensorSquare.sg31335`, `OAI.UniversalTensorSquare.sg31422`, `OAI.UniversalTensorSquare.sg35213`, `OAI.UniversalTensorSquare.sg35216`, `OAI.UniversalTensorSquare.sg35324`, `OAI.UniversalTensorSquare.sg36249`, `OAI.UniversalTensorSquare.sg36250`, `OAI.UniversalTensorSquare.sg36997`, `OAI.UniversalTensorSquare.sg36998`, `OAI.UniversalTensorSquare.sg38330`, `OAI.UniversalTensorSquare.sg38331`, `OAI.UniversalTensorSquare.sg40742` and `OAI.UniversalTensorSquare.sg42530` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg537)

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

lemma sg537 : RowSquare [4,2,1,1,1] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
