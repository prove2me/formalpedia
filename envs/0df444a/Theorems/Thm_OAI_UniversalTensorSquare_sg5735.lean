-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg5735
-- name    : OAI.UniversalTensorSquare.sg5735
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:22:37.812229+00:00
-- url     : https://prove2.me/theorems/22ca3ff0-78d3-4e62-9db6-4f7e1f56a156
-- title:
--   OAI.UniversalTensorSquare.sg5735: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg5735` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg5735 : RowSquare [8,3,2,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_109All`, `OAI.UniversalTensorSquare.degreeTree39_57All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_72All`, `OAI.UniversalTensorSquare.degreeTree39_87All`, `OAI.UniversalTensorSquare.degreeTree39_99All`, `OAI.UniversalTensorSquare.degreeTree43_209All`, `OAI.UniversalTensorSquare.degreeTree43_215All`, `OAI.UniversalTensorSquare.degreeTree43_218All`, `OAI.UniversalTensorSquare.degreeTree43_226All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_230All`, `OAI.UniversalTensorSquare.degreeTree43_330All`, `OAI.UniversalTensorSquare.degreeTree43_335All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_347All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree43_356All`, `OAI.UniversalTensorSquare.degreeTree43_358All`, `OAI.UniversalTensorSquare.degreeTree43_361All`, `OAI.UniversalTensorSquare.degreeTree43_382All`, `OAI.UniversalTensorSquare.degreeTree43_392All`, `OAI.UniversalTensorSquare.degreeTree43_394All`, `OAI.UniversalTensorSquare.degreeTree43_409All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_413All`, `OAI.UniversalTensorSquare.degreeTree43_416All`, `OAI.UniversalTensorSquare.degreeTree43_420All`, `OAI.UniversalTensorSquare.degreeTree43_432All`, `OAI.UniversalTensorSquare.degreeTree43_437All`, `OAI.UniversalTensorSquare.degreeTree43_445All`, `OAI.UniversalTensorSquare.degreeTree43_461All`, `OAI.UniversalTensorSquare.degreeTree43_463All`, `OAI.UniversalTensorSquare.degreeTree43_465All`, `OAI.UniversalTensorSquare.degreeTree43_471All`, `OAI.UniversalTensorSquare.degreeTree43_476All`, `OAI.UniversalTensorSquare.degreeTree43_479All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degreeTree43_507All`, `OAI.UniversalTensorSquare.degreeTree43_520All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree43_556All`, `OAI.UniversalTensorSquare.degreeTree43_561All`, `OAI.UniversalTensorSquare.degreeTree43_570All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree43_609All`, `OAI.UniversalTensorSquare.degreeTree43_611All`, `OAI.UniversalTensorSquare.degreeTree43_612All`, `OAI.UniversalTensorSquare.degreeTree43_615All`, `OAI.UniversalTensorSquare.degreeTree43_621All`, `OAI.UniversalTensorSquare.degreeTree43_625All`, `OAI.UniversalTensorSquare.degreeTree43_628All`, `OAI.UniversalTensorSquare.degreeTree43_630All`, `OAI.UniversalTensorSquare.degreeTree43_631All`, `OAI.UniversalTensorSquare.degreeTree43_635All`, `OAI.UniversalTensorSquare.degreeTree43_637All`, `OAI.UniversalTensorSquare.degreeTree43_640All`, `OAI.UniversalTensorSquare.degreeTree43_642All`, `OAI.UniversalTensorSquare.sg23031`, `OAI.UniversalTensorSquare.sg25812`, `OAI.UniversalTensorSquare.sg25959`, `OAI.UniversalTensorSquare.sg26014`, `OAI.UniversalTensorSquare.sg26091`, `OAI.UniversalTensorSquare.sg26320`, `OAI.UniversalTensorSquare.sg26345`, `OAI.UniversalTensorSquare.sg28108`, `OAI.UniversalTensorSquare.sg28241`, `OAI.UniversalTensorSquare.sg28304`, `OAI.UniversalTensorSquare.sg28515`, `OAI.UniversalTensorSquare.sg28573`, `OAI.UniversalTensorSquare.sg28654`, `OAI.UniversalTensorSquare.sg28692`, `OAI.UniversalTensorSquare.sg28759`, `OAI.UniversalTensorSquare.sg28766`, `OAI.UniversalTensorSquare.sg28918`, `OAI.UniversalTensorSquare.sg28979`, `OAI.UniversalTensorSquare.sg29231`, `OAI.UniversalTensorSquare.sg29263`, `OAI.UniversalTensorSquare.sg29289`, `OAI.UniversalTensorSquare.sg29355`, `OAI.UniversalTensorSquare.sg29383`, `OAI.UniversalTensorSquare.sg29390`, `OAI.UniversalTensorSquare.sg29413`, `OAI.UniversalTensorSquare.sg29458`, `OAI.UniversalTensorSquare.sg29555`, `OAI.UniversalTensorSquare.sg30034`, `OAI.UniversalTensorSquare.sg30040`, `OAI.UniversalTensorSquare.sg30062`, `OAI.UniversalTensorSquare.sg30069`, `OAI.UniversalTensorSquare.sg30149`, `OAI.UniversalTensorSquare.sg30174`, `OAI.UniversalTensorSquare.sg30181`, `OAI.UniversalTensorSquare.sg30232`, `OAI.UniversalTensorSquare.sg30306`, `OAI.UniversalTensorSquare.sg30313`, `OAI.UniversalTensorSquare.sg30335`, `OAI.UniversalTensorSquare.sg30381`, `OAI.UniversalTensorSquare.sg30472`, `OAI.UniversalTensorSquare.sg30497`, `OAI.UniversalTensorSquare.sg30870`, `OAI.UniversalTensorSquare.sg30899`, `OAI.UniversalTensorSquare.sg30989`, `OAI.UniversalTensorSquare.sg30997`, `OAI.UniversalTensorSquare.sg31022`, `OAI.UniversalTensorSquare.sg31605`, `OAI.UniversalTensorSquare.sg31638`, `OAI.UniversalTensorSquare.sg31719`, `OAI.UniversalTensorSquare.sg31773`, `OAI.UniversalTensorSquare.sg31810`, `OAI.UniversalTensorSquare.sg31818`, `OAI.UniversalTensorSquare.sg31844`, `OAI.UniversalTensorSquare.sg31879`, `OAI.UniversalTensorSquare.sg31887`, `OAI.UniversalTensorSquare.sg31893`, `OAI.UniversalTensorSquare.sg31905`, `OAI.UniversalTensorSquare.sg31910`, `OAI.UniversalTensorSquare.sg31920`, `OAI.UniversalTensorSquare.sg31921` and `OAI.UniversalTensorSquare.sg31924` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg5735)

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

lemma sg5735 : RowSquare [8,3,2,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
