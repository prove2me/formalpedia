-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg265
-- name    : OAI.UniversalTensorSquare.sg265
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T10:20:04.594551+00:00
-- url     : https://prove2.me/theorems/22590484-0505-4be4-9a03-c9c8cef0ff66
-- title:
--   OAI.UniversalTensorSquare.sg265: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg265` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg265 : RowSquare [3,1,1,1,1,1] [5,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_243All`, `OAI.UniversalTensorSquare.degreeTree43_264All`, `OAI.UniversalTensorSquare.degreeTree43_35All`, `OAI.UniversalTensorSquare.degreeTree43_44All`, `OAI.UniversalTensorSquare.degreeTree43_480All`, `OAI.UniversalTensorSquare.degreeTree43_60All`, `OAI.UniversalTensorSquare.degreeTree43_630All`, `OAI.UniversalTensorSquare.degreeTree43_70All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree43_99All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_19All`, `OAI.UniversalTensorSquare.degreeTree62_200All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_371All`, `OAI.UniversalTensorSquare.degreeTree62_372All`, `OAI.UniversalTensorSquare.degreeTree62_38All`, `OAI.UniversalTensorSquare.degreeTree62_426All`, `OAI.UniversalTensorSquare.degreeTree62_496All`, `OAI.UniversalTensorSquare.degreeTree62_521All`, `OAI.UniversalTensorSquare.degreeTree62_530All`, `OAI.UniversalTensorSquare.degreeTree62_56All`, `OAI.UniversalTensorSquare.degreeTree62_654All`, `OAI.UniversalTensorSquare.degreeTree62_67All`, `OAI.UniversalTensorSquare.degreeTree62_70All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_823All`, `OAI.UniversalTensorSquare.degreeTree62_869All`, `OAI.UniversalTensorSquare.degreeTree62_94All`, `OAI.UniversalTensorSquare.sg10215`, `OAI.UniversalTensorSquare.sg10222`, `OAI.UniversalTensorSquare.sg10225`, `OAI.UniversalTensorSquare.sg1330`, `OAI.UniversalTensorSquare.sg23694`, `OAI.UniversalTensorSquare.sg23962`, `OAI.UniversalTensorSquare.sg24054`, `OAI.UniversalTensorSquare.sg24179`, `OAI.UniversalTensorSquare.sg24200`, `OAI.UniversalTensorSquare.sg24211`, `OAI.UniversalTensorSquare.sg24369`, `OAI.UniversalTensorSquare.sg24385`, `OAI.UniversalTensorSquare.sg24393`, `OAI.UniversalTensorSquare.sg24462`, `OAI.UniversalTensorSquare.sg24476`, `OAI.UniversalTensorSquare.sg24483`, `OAI.UniversalTensorSquare.sg24562`, `OAI.UniversalTensorSquare.sg24564`, `OAI.UniversalTensorSquare.sg24636`, `OAI.UniversalTensorSquare.sg24637`, `OAI.UniversalTensorSquare.sg24638`, `OAI.UniversalTensorSquare.sg24731`, `OAI.UniversalTensorSquare.sg24738`, `OAI.UniversalTensorSquare.sg24739`, `OAI.UniversalTensorSquare.sg24745`, `OAI.UniversalTensorSquare.sg24923`, `OAI.UniversalTensorSquare.sg24930`, `OAI.UniversalTensorSquare.sg24996`, `OAI.UniversalTensorSquare.sg25012`, `OAI.UniversalTensorSquare.sg25069`, `OAI.UniversalTensorSquare.sg25156`, `OAI.UniversalTensorSquare.sg25216`, `OAI.UniversalTensorSquare.sg25220`, `OAI.UniversalTensorSquare.sg25227`, `OAI.UniversalTensorSquare.sg25266`, `OAI.UniversalTensorSquare.sg25286`, `OAI.UniversalTensorSquare.sg25322`, `OAI.UniversalTensorSquare.sg25761`, `OAI.UniversalTensorSquare.sg26007`, `OAI.UniversalTensorSquare.sg31966`, `OAI.UniversalTensorSquare.sg32385`, `OAI.UniversalTensorSquare.sg32412`, `OAI.UniversalTensorSquare.sg35620`, `OAI.UniversalTensorSquare.sg35622`, `OAI.UniversalTensorSquare.sg38100` and `OAI.UniversalTensorSquare.sg9712` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg265)

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

lemma sg265 : RowSquare [3,1,1,1,1,1] [5,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
