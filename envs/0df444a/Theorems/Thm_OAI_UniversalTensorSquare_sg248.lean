-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg248
-- name    : OAI.UniversalTensorSquare.sg248
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T02:49:41.397319+00:00
-- url     : https://prove2.me/theorems/9a0e77fd-1a6d-4161-bc67-6a69ac1d4527
-- title:
--   OAI.UniversalTensorSquare.sg248: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg248` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg248 : RowSquare [2,2,1,1,1,1] [8]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_123All`, `OAI.UniversalTensorSquare.degreeTree39_124All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree39_90All`, `OAI.UniversalTensorSquare.degreeTree39_92All`, `OAI.UniversalTensorSquare.degreeTree43_348All`, `OAI.UniversalTensorSquare.degreeTreeAll39`, `OAI.UniversalTensorSquare.sg11957`, `OAI.UniversalTensorSquare.sg11968`, `OAI.UniversalTensorSquare.sg12011`, `OAI.UniversalTensorSquare.sg12017`, `OAI.UniversalTensorSquare.sg12021`, `OAI.UniversalTensorSquare.sg12055`, `OAI.UniversalTensorSquare.sg12157`, `OAI.UniversalTensorSquare.sg12178`, `OAI.UniversalTensorSquare.sg22454`, `OAI.UniversalTensorSquare.sg22458`, `OAI.UniversalTensorSquare.sg22495`, `OAI.UniversalTensorSquare.sg22500`, `OAI.UniversalTensorSquare.sg22501`, `OAI.UniversalTensorSquare.sg22504`, `OAI.UniversalTensorSquare.sg22505`, `OAI.UniversalTensorSquare.sg22506`, `OAI.UniversalTensorSquare.sg22508`, `OAI.UniversalTensorSquare.sg22529`, `OAI.UniversalTensorSquare.sg22535`, `OAI.UniversalTensorSquare.sg22540`, `OAI.UniversalTensorSquare.sg22545`, `OAI.UniversalTensorSquare.sg22555`, `OAI.UniversalTensorSquare.sg22562`, `OAI.UniversalTensorSquare.sg22568`, `OAI.UniversalTensorSquare.sg22585`, `OAI.UniversalTensorSquare.sg22641`, `OAI.UniversalTensorSquare.sg22647`, `OAI.UniversalTensorSquare.sg22648`, `OAI.UniversalTensorSquare.sg22652`, `OAI.UniversalTensorSquare.sg22653`, `OAI.UniversalTensorSquare.sg22656`, `OAI.UniversalTensorSquare.sg22657`, `OAI.UniversalTensorSquare.sg22674`, `OAI.UniversalTensorSquare.sg22681`, `OAI.UniversalTensorSquare.sg22682`, `OAI.UniversalTensorSquare.sg22687`, `OAI.UniversalTensorSquare.sg22691`, `OAI.UniversalTensorSquare.sg22692`, `OAI.UniversalTensorSquare.sg22693`, `OAI.UniversalTensorSquare.sg22705`, `OAI.UniversalTensorSquare.sg22706`, `OAI.UniversalTensorSquare.sg22712`, `OAI.UniversalTensorSquare.sg22713`, `OAI.UniversalTensorSquare.sg22714`, `OAI.UniversalTensorSquare.sg22718`, `OAI.UniversalTensorSquare.sg22719`, `OAI.UniversalTensorSquare.sg22732`, `OAI.UniversalTensorSquare.sg22733`, `OAI.UniversalTensorSquare.sg22734`, `OAI.UniversalTensorSquare.sg22770`, `OAI.UniversalTensorSquare.sg22777`, `OAI.UniversalTensorSquare.sg22782`, `OAI.UniversalTensorSquare.sg22784`, `OAI.UniversalTensorSquare.sg22799`, `OAI.UniversalTensorSquare.sg22805`, `OAI.UniversalTensorSquare.sg22807`, `OAI.UniversalTensorSquare.sg22810`, `OAI.UniversalTensorSquare.sg22822`, `OAI.UniversalTensorSquare.sg22852`, `OAI.UniversalTensorSquare.sg22866`, `OAI.UniversalTensorSquare.sg22911`, `OAI.UniversalTensorSquare.sg22919`, `OAI.UniversalTensorSquare.sg22924`, `OAI.UniversalTensorSquare.sg22925`, `OAI.UniversalTensorSquare.sg22929`, `OAI.UniversalTensorSquare.sg22942`, `OAI.UniversalTensorSquare.sg22950`, `OAI.UniversalTensorSquare.sg22956`, `OAI.UniversalTensorSquare.sg22957`, `OAI.UniversalTensorSquare.sg22958`, `OAI.UniversalTensorSquare.sg22961`, `OAI.UniversalTensorSquare.sg22962`, `OAI.UniversalTensorSquare.sg22963`, `OAI.UniversalTensorSquare.sg22966`, `OAI.UniversalTensorSquare.sg22978`, `OAI.UniversalTensorSquare.sg22979`, `OAI.UniversalTensorSquare.sg22985`, `OAI.UniversalTensorSquare.sg22989`, `OAI.UniversalTensorSquare.sg22990`, `OAI.UniversalTensorSquare.sg23001`, `OAI.UniversalTensorSquare.sg23002`, `OAI.UniversalTensorSquare.sg23026`, `OAI.UniversalTensorSquare.sg23034`, `OAI.UniversalTensorSquare.sg23035`, `OAI.UniversalTensorSquare.sg23040`, `OAI.UniversalTensorSquare.sg23041`, `OAI.UniversalTensorSquare.sg23042`, `OAI.UniversalTensorSquare.sg23045`, `OAI.UniversalTensorSquare.sg23046`, `OAI.UniversalTensorSquare.sg23059`, `OAI.UniversalTensorSquare.sg23060`, `OAI.UniversalTensorSquare.sg23061`, `OAI.UniversalTensorSquare.sg23066`, `OAI.UniversalTensorSquare.sg23070`, `OAI.UniversalTensorSquare.sg23079`, `OAI.UniversalTensorSquare.sg23080`, `OAI.UniversalTensorSquare.sg23097`, `OAI.UniversalTensorSquare.sg23102`, `OAI.UniversalTensorSquare.sg23103`, `OAI.UniversalTensorSquare.sg23114`, `OAI.UniversalTensorSquare.sg23143`, `OAI.UniversalTensorSquare.sg23145`, `OAI.UniversalTensorSquare.sg23149`, `OAI.UniversalTensorSquare.sg23165`, `OAI.UniversalTensorSquare.sg23170`, `OAI.UniversalTensorSquare.sg23194`, `OAI.UniversalTensorSquare.sg23255`, `OAI.UniversalTensorSquare.sg23267`, `OAI.UniversalTensorSquare.sg23284`, `OAI.UniversalTensorSquare.sg23292`, `OAI.UniversalTensorSquare.sg23293`, `OAI.UniversalTensorSquare.sg23303`, `OAI.UniversalTensorSquare.sg23317`, `OAI.UniversalTensorSquare.sg23337`, `OAI.UniversalTensorSquare.sg27668`, `OAI.UniversalTensorSquare.sg27730`, `OAI.UniversalTensorSquare.sg27735`, `OAI.UniversalTensorSquare.sg27739`, `OAI.UniversalTensorSquare.sg27782`, `OAI.UniversalTensorSquare.sg27791`, `OAI.UniversalTensorSquare.sg27823`, `OAI.UniversalTensorSquare.sg27834`, `OAI.UniversalTensorSquare.sg27851`, `OAI.UniversalTensorSquare.sg27864`, `OAI.UniversalTensorSquare.sg27964`, `OAI.UniversalTensorSquare.sg27970`, `OAI.UniversalTensorSquare.sg28014`, `OAI.UniversalTensorSquare.sg28021`, `OAI.UniversalTensorSquare.sg28028`, `OAI.UniversalTensorSquare.sg28052`, `OAI.UniversalTensorSquare.sg28060`, `OAI.UniversalTensorSquare.sg28085`, `OAI.UniversalTensorSquare.sg28096`, `OAI.UniversalTensorSquare.sg28174`, `OAI.UniversalTensorSquare.sg28184`, `OAI.UniversalTensorSquare.sg28209`, `OAI.UniversalTensorSquare.sg28221`, `OAI.UniversalTensorSquare.sg28225`, `OAI.UniversalTensorSquare.sg28244`, `OAI.UniversalTensorSquare.sg28312`, `OAI.UniversalTensorSquare.sg28333`, `OAI.UniversalTensorSquare.sg28337`, `OAI.UniversalTensorSquare.sg28376`, `OAI.UniversalTensorSquare.sg28465`, `OAI.UniversalTensorSquare.sg28513`, `OAI.UniversalTensorSquare.sg28548`, `OAI.UniversalTensorSquare.sg31655` and `OAI.UniversalTensorSquare.sg33754` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg248)

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

lemma sg248 : RowSquare [2,2,1,1,1,1] [8] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
