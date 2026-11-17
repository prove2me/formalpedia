-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg324
-- name    : OAI.UniversalTensorSquare.sg324
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T03:00:56.808138+00:00
-- url     : https://prove2.me/theorems/521eec52-78af-4ca0-a359-1dab35c26032
-- title:
--   OAI.UniversalTensorSquare.sg324: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg324` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg324 : RowSquare [4,1,1,1,1] [4,4]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_198All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_243All`, `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree43_264All`, `OAI.UniversalTensorSquare.degreeTree43_280All`, `OAI.UniversalTensorSquare.degreeTree43_306All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_425All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_483All`, `OAI.UniversalTensorSquare.degreeTree43_489All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree43_590All`, `OAI.UniversalTensorSquare.degreeTree43_599All`, `OAI.UniversalTensorSquare.degreeTree43_614All`, `OAI.UniversalTensorSquare.degreeTree43_645All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.degreeTree43_95All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_184All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_47All`, `OAI.UniversalTensorSquare.degreeTree62_52All`, `OAI.UniversalTensorSquare.degreeTree62_597All`, `OAI.UniversalTensorSquare.degreeTree62_599All`, `OAI.UniversalTensorSquare.degreeTree62_615All`, `OAI.UniversalTensorSquare.degreeTree62_617All`, `OAI.UniversalTensorSquare.degreeTree62_670All`, `OAI.UniversalTensorSquare.degreeTree62_717All`, `OAI.UniversalTensorSquare.sg10105`, `OAI.UniversalTensorSquare.sg15748`, `OAI.UniversalTensorSquare.sg21704`, `OAI.UniversalTensorSquare.sg21727`, `OAI.UniversalTensorSquare.sg21753`, `OAI.UniversalTensorSquare.sg21882`, `OAI.UniversalTensorSquare.sg22116`, `OAI.UniversalTensorSquare.sg22193`, `OAI.UniversalTensorSquare.sg23322`, `OAI.UniversalTensorSquare.sg23600`, `OAI.UniversalTensorSquare.sg23631`, `OAI.UniversalTensorSquare.sg23634`, `OAI.UniversalTensorSquare.sg24398`, `OAI.UniversalTensorSquare.sg24450`, `OAI.UniversalTensorSquare.sg24467`, `OAI.UniversalTensorSquare.sg25359`, `OAI.UniversalTensorSquare.sg25480`, `OAI.UniversalTensorSquare.sg25961`, `OAI.UniversalTensorSquare.sg26517`, `OAI.UniversalTensorSquare.sg26955`, `OAI.UniversalTensorSquare.sg27007`, `OAI.UniversalTensorSquare.sg27275`, `OAI.UniversalTensorSquare.sg27940`, `OAI.UniversalTensorSquare.sg28798`, `OAI.UniversalTensorSquare.sg28803`, `OAI.UniversalTensorSquare.sg28807`, `OAI.UniversalTensorSquare.sg29094`, `OAI.UniversalTensorSquare.sg29195`, `OAI.UniversalTensorSquare.sg29392`, `OAI.UniversalTensorSquare.sg29482`, `OAI.UniversalTensorSquare.sg29496`, `OAI.UniversalTensorSquare.sg29589`, `OAI.UniversalTensorSquare.sg29590`, `OAI.UniversalTensorSquare.sg29647`, `OAI.UniversalTensorSquare.sg29737`, `OAI.UniversalTensorSquare.sg29808`, `OAI.UniversalTensorSquare.sg29940`, `OAI.UniversalTensorSquare.sg30071`, `OAI.UniversalTensorSquare.sg30183`, `OAI.UniversalTensorSquare.sg31145`, `OAI.UniversalTensorSquare.sg31204`, `OAI.UniversalTensorSquare.sg31293`, `OAI.UniversalTensorSquare.sg31319`, `OAI.UniversalTensorSquare.sg31381`, `OAI.UniversalTensorSquare.sg31398`, `OAI.UniversalTensorSquare.sg31607`, `OAI.UniversalTensorSquare.sg31612`, `OAI.UniversalTensorSquare.sg31911`, `OAI.UniversalTensorSquare.sg41777` and `OAI.UniversalTensorSquare.sg6942` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg324)

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

lemma sg324 : RowSquare [4,1,1,1,1] [4,4] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
