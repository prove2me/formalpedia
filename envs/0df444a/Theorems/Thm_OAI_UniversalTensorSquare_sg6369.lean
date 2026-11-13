-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg6369
-- name    : OAI.UniversalTensorSquare.sg6369
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:25:05.220724+00:00
-- url     : https://prove2.me/theorems/29431b01-e647-479e-afa1-4e3615f88bd9
-- title:
--   OAI.UniversalTensorSquare.sg6369: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg6369` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg6369 : RowSquare [6,4,2,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_51All`, `OAI.UniversalTensorSquare.degreeTree39_54All`, `OAI.UniversalTensorSquare.degreeTree39_55All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_66All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_73All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree39_81All`, `OAI.UniversalTensorSquare.degreeTree39_83All`, `OAI.UniversalTensorSquare.sg22457`, `OAI.UniversalTensorSquare.sg22487`, `OAI.UniversalTensorSquare.sg22499`, `OAI.UniversalTensorSquare.sg22534`, `OAI.UniversalTensorSquare.sg22561`, `OAI.UniversalTensorSquare.sg22567`, `OAI.UniversalTensorSquare.sg22584`, `OAI.UniversalTensorSquare.sg22646`, `OAI.UniversalTensorSquare.sg22673`, `OAI.UniversalTensorSquare.sg22680`, `OAI.UniversalTensorSquare.sg22686`, `OAI.UniversalTensorSquare.sg22704`, `OAI.UniversalTensorSquare.sg22716`, `OAI.UniversalTensorSquare.sg22731`, `OAI.UniversalTensorSquare.sg22762`, `OAI.UniversalTensorSquare.sg22769`, `OAI.UniversalTensorSquare.sg22776`, `OAI.UniversalTensorSquare.sg22798`, `OAI.UniversalTensorSquare.sg22821`, `OAI.UniversalTensorSquare.sg22845`, `OAI.UniversalTensorSquare.sg22851`, `OAI.UniversalTensorSquare.sg22917`, `OAI.UniversalTensorSquare.sg22941`, `OAI.UniversalTensorSquare.sg22948`, `OAI.UniversalTensorSquare.sg22955`, `OAI.UniversalTensorSquare.sg22960`, `OAI.UniversalTensorSquare.sg22977`, `OAI.UniversalTensorSquare.sg22983`, `OAI.UniversalTensorSquare.sg23000`, `OAI.UniversalTensorSquare.sg23025`, `OAI.UniversalTensorSquare.sg23033`, `OAI.UniversalTensorSquare.sg23039`, `OAI.UniversalTensorSquare.sg23058`, `OAI.UniversalTensorSquare.sg23064`, `OAI.UniversalTensorSquare.sg23096`, `OAI.UniversalTensorSquare.sg23135`, `OAI.UniversalTensorSquare.sg23142`, `OAI.UniversalTensorSquare.sg23148`, `OAI.UniversalTensorSquare.sg23164`, `OAI.UniversalTensorSquare.sg23193`, `OAI.UniversalTensorSquare.sg23239`, `OAI.UniversalTensorSquare.sg23246`, `OAI.UniversalTensorSquare.sg23253`, `OAI.UniversalTensorSquare.sg23265`, `OAI.UniversalTensorSquare.sg23282`, `OAI.UniversalTensorSquare.sg23290`, `OAI.UniversalTensorSquare.sg23296`, `OAI.UniversalTensorSquare.sg23315` and `OAI.UniversalTensorSquare.sg23321` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean (declaration OAI.UniversalTensorSquare.sg6369)

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

lemma sg6369 : RowSquare [6,4,2,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
