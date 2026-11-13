-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg789
-- name    : OAI.UniversalTensorSquare.sg789
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:41:19.641306+00:00
-- url     : https://prove2.me/theorems/0513d7fb-0615-4c06-b86d-9e7fc5d533bd
-- title:
--   OAI.UniversalTensorSquare.sg789: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg789` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg789 : RowSquare [3,3,1,1,1,1] [10]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree24_2All`, `OAI.UniversalTensorSquare.degreeTree26_0All`, `OAI.UniversalTensorSquare.degreeTree26_27All`, `OAI.UniversalTensorSquare.degreeTree26_42All`, `OAI.UniversalTensorSquare.degreeTree26_5All`, `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree39_51All`, `OAI.UniversalTensorSquare.degreeTree39_60All`, `OAI.UniversalTensorSquare.degreeTree39_63All`, `OAI.UniversalTensorSquare.degreeTree39_81All`, `OAI.UniversalTensorSquare.degreeTree43_101All`, `OAI.UniversalTensorSquare.degreeTree43_111All`, `OAI.UniversalTensorSquare.degreeTree43_263All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_324All`, `OAI.UniversalTensorSquare.degreeTree43_330All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_347All`, `OAI.UniversalTensorSquare.degreeTree43_351All`, `OAI.UniversalTensorSquare.degreeTree43_356All`, `OAI.UniversalTensorSquare.degreeTree43_361All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_377All`, `OAI.UniversalTensorSquare.degreeTree43_378All`, `OAI.UniversalTensorSquare.degreeTree43_428All`, `OAI.UniversalTensorSquare.degreeTree43_431All`, `OAI.UniversalTensorSquare.degreeTree43_432All`, `OAI.UniversalTensorSquare.degreeTree43_434All`, `OAI.UniversalTensorSquare.degreeTree43_484All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degreeTree43_501All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.sg12984`, `OAI.UniversalTensorSquare.sg22438`, `OAI.UniversalTensorSquare.sg22444`, `OAI.UniversalTensorSquare.sg23391`, `OAI.UniversalTensorSquare.sg23399`, `OAI.UniversalTensorSquare.sg24804`, `OAI.UniversalTensorSquare.sg25912`, `OAI.UniversalTensorSquare.sg25930`, `OAI.UniversalTensorSquare.sg25934`, `OAI.UniversalTensorSquare.sg26305`, `OAI.UniversalTensorSquare.sg26993`, `OAI.UniversalTensorSquare.sg27100`, `OAI.UniversalTensorSquare.sg27335`, `OAI.UniversalTensorSquare.sg27819`, `OAI.UniversalTensorSquare.sg27847`, `OAI.UniversalTensorSquare.sg28010`, `OAI.UniversalTensorSquare.sg28048`, `OAI.UniversalTensorSquare.sg28055`, `OAI.UniversalTensorSquare.sg28080`, `OAI.UniversalTensorSquare.sg28163`, `OAI.UniversalTensorSquare.sg28170`, `OAI.UniversalTensorSquare.sg28205`, `OAI.UniversalTensorSquare.sg28492`, `OAI.UniversalTensorSquare.sg28508`, `OAI.UniversalTensorSquare.sg28543`, `OAI.UniversalTensorSquare.sg28550`, `OAI.UniversalTensorSquare.sg28628`, `OAI.UniversalTensorSquare.sg28646`, `OAI.UniversalTensorSquare.sg28653`, `OAI.UniversalTensorSquare.sg28685`, `OAI.UniversalTensorSquare.sg28882`, `OAI.UniversalTensorSquare.sg29178`, `OAI.UniversalTensorSquare.sg29205`, `OAI.UniversalTensorSquare.sg29262`, `OAI.UniversalTensorSquare.sg29337`, `OAI.UniversalTensorSquare.sg29540`, `OAI.UniversalTensorSquare.sg30016`, `OAI.UniversalTensorSquare.sg7847` and `OAI.UniversalTensorSquare.sg7853` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg789)

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

lemma sg789 : RowSquare [3,3,1,1,1,1] [10] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
