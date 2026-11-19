-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg808
-- name    : OAI.UniversalTensorSquare.sg808
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:35:48.295806+00:00
-- url     : https://prove2.me/theorems/f1b4f956-f9da-4e1b-84e1-cad2ea3a05c0
-- title:
--   OAI.UniversalTensorSquare.sg808: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg808` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg808 : RowSquare [4,2,1,1,1,1] [2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_107All`, `OAI.UniversalTensorSquare.degreeTree43_117All`, `OAI.UniversalTensorSquare.degreeTree43_120All`, `OAI.UniversalTensorSquare.degreeTree43_128All`, `OAI.UniversalTensorSquare.degreeTree43_129All`, `OAI.UniversalTensorSquare.degreeTree43_194All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_198All`, `OAI.UniversalTensorSquare.degreeTree43_201All`, `OAI.UniversalTensorSquare.degreeTree43_224All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_243All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_35All`, `OAI.UniversalTensorSquare.degreeTree43_44All`, `OAI.UniversalTensorSquare.degreeTree43_473All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_544All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_609All`, `OAI.UniversalTensorSquare.degreeTree43_60All`, `OAI.UniversalTensorSquare.degreeTree43_61All`, `OAI.UniversalTensorSquare.degreeTree43_70All`, `OAI.UniversalTensorSquare.degreeTree43_95All`, `OAI.UniversalTensorSquare.degreeTree62_923All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.sg11842`, `OAI.UniversalTensorSquare.sg11849`, `OAI.UniversalTensorSquare.sg11856`, `OAI.UniversalTensorSquare.sg11863`, `OAI.UniversalTensorSquare.sg11868`, `OAI.UniversalTensorSquare.sg11952`, `OAI.UniversalTensorSquare.sg12006`, `OAI.UniversalTensorSquare.sg12040`, `OAI.UniversalTensorSquare.sg21731`, `OAI.UniversalTensorSquare.sg21864`, `OAI.UniversalTensorSquare.sg21882`, `OAI.UniversalTensorSquare.sg21925`, `OAI.UniversalTensorSquare.sg24538`, `OAI.UniversalTensorSquare.sg24665`, `OAI.UniversalTensorSquare.sg24693`, `OAI.UniversalTensorSquare.sg24715`, `OAI.UniversalTensorSquare.sg25053`, `OAI.UniversalTensorSquare.sg25054`, `OAI.UniversalTensorSquare.sg25064`, `OAI.UniversalTensorSquare.sg25216`, `OAI.UniversalTensorSquare.sg25314`, `OAI.UniversalTensorSquare.sg25354`, `OAI.UniversalTensorSquare.sg25548`, `OAI.UniversalTensorSquare.sg25703`, `OAI.UniversalTensorSquare.sg25768`, `OAI.UniversalTensorSquare.sg27262`, `OAI.UniversalTensorSquare.sg27291`, `OAI.UniversalTensorSquare.sg27498`, `OAI.UniversalTensorSquare.sg31223`, `OAI.UniversalTensorSquare.sg31299`, `OAI.UniversalTensorSquare.sg31336`, `OAI.UniversalTensorSquare.sg32530`, `OAI.UniversalTensorSquare.sg32536`, `OAI.UniversalTensorSquare.sg34521`, `OAI.UniversalTensorSquare.sg34525`, `OAI.UniversalTensorSquare.sg35208`, `OAI.UniversalTensorSquare.sg4303`, `OAI.UniversalTensorSquare.sg6409` and `OAI.UniversalTensorSquare.sg8721` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg808)

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

lemma sg808 : RowSquare [4,2,1,1,1,1] [2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
