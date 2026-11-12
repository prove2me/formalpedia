-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1416
-- name    : OAI.UniversalTensorSquare.sg1416
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:17:22.310011+00:00
-- url     : https://prove2.me/theorems/5d69b197-5335-47ba-a6cd-869198b937b3
-- title:
--   OAI.UniversalTensorSquare.sg1416: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1416` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1416 : RowSquare [6,3,1,1] [2,2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_9All`, `OAI.UniversalTensorSquare.degreeTree43_117All`, `OAI.UniversalTensorSquare.degreeTree43_122All`, `OAI.UniversalTensorSquare.degreeTree43_15All`, `OAI.UniversalTensorSquare.degreeTree43_16All`, `OAI.UniversalTensorSquare.degreeTree43_280All`, `OAI.UniversalTensorSquare.degreeTree43_44All`, `OAI.UniversalTensorSquare.degreeTree43_51All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree62_105All`, `OAI.UniversalTensorSquare.degreeTree62_232All`, `OAI.UniversalTensorSquare.degreeTree62_352All`, `OAI.UniversalTensorSquare.degreeTree62_363All`, `OAI.UniversalTensorSquare.degreeTree62_420All`, `OAI.UniversalTensorSquare.degreeTree62_462All`, `OAI.UniversalTensorSquare.degreeTree62_760All`, `OAI.UniversalTensorSquare.degreeTree62_796All`, `OAI.UniversalTensorSquare.degreeTree62_846All`, `OAI.UniversalTensorSquare.degreeTree62_903All`, `OAI.UniversalTensorSquare.degreeTree62_929All`, `OAI.UniversalTensorSquare.sg18372`, `OAI.UniversalTensorSquare.sg18654`, `OAI.UniversalTensorSquare.sg21728`, `OAI.UniversalTensorSquare.sg21882`, `OAI.UniversalTensorSquare.sg21886`, `OAI.UniversalTensorSquare.sg23858`, `OAI.UniversalTensorSquare.sg23875`, `OAI.UniversalTensorSquare.sg23888`, `OAI.UniversalTensorSquare.sg23889`, `OAI.UniversalTensorSquare.sg24222`, `OAI.UniversalTensorSquare.sg24226`, `OAI.UniversalTensorSquare.sg24240`, `OAI.UniversalTensorSquare.sg24259`, `OAI.UniversalTensorSquare.sg24271`, `OAI.UniversalTensorSquare.sg24275`, `OAI.UniversalTensorSquare.sg24355`, `OAI.UniversalTensorSquare.sg24379`, `OAI.UniversalTensorSquare.sg24789`, `OAI.UniversalTensorSquare.sg24856`, `OAI.UniversalTensorSquare.sg24910`, `OAI.UniversalTensorSquare.sg25013`, `OAI.UniversalTensorSquare.sg25111`, `OAI.UniversalTensorSquare.sg25135`, `OAI.UniversalTensorSquare.sg25142`, `OAI.UniversalTensorSquare.sg25148`, `OAI.UniversalTensorSquare.sg25171`, `OAI.UniversalTensorSquare.sg26811`, `OAI.UniversalTensorSquare.sg26836`, `OAI.UniversalTensorSquare.sg30629`, `OAI.UniversalTensorSquare.sg34664`, `OAI.UniversalTensorSquare.sg34669`, `OAI.UniversalTensorSquare.sg34671`, `OAI.UniversalTensorSquare.sg35906`, `OAI.UniversalTensorSquare.sg35910`, `OAI.UniversalTensorSquare.sg35912`, `OAI.UniversalTensorSquare.sg35939`, `OAI.UniversalTensorSquare.sg35942`, `OAI.UniversalTensorSquare.sg35944`, `OAI.UniversalTensorSquare.sg35968`, `OAI.UniversalTensorSquare.sg35973`, `OAI.UniversalTensorSquare.sg36449`, `OAI.UniversalTensorSquare.sg36452`, `OAI.UniversalTensorSquare.sg36454`, `OAI.UniversalTensorSquare.sg36622`, `OAI.UniversalTensorSquare.sg36626`, `OAI.UniversalTensorSquare.sg36628`, `OAI.UniversalTensorSquare.sg36637`, `OAI.UniversalTensorSquare.sg36642`, `OAI.UniversalTensorSquare.sg36644`, `OAI.UniversalTensorSquare.sg37077`, `OAI.UniversalTensorSquare.sg37082`, `OAI.UniversalTensorSquare.sg37084`, `OAI.UniversalTensorSquare.sg38004`, `OAI.UniversalTensorSquare.sg38007`, `OAI.UniversalTensorSquare.sg38009`, `OAI.UniversalTensorSquare.sg40000`, `OAI.UniversalTensorSquare.sg40003`, `OAI.UniversalTensorSquare.sg40004`, `OAI.UniversalTensorSquare.sg40408`, `OAI.UniversalTensorSquare.sg40409`, `OAI.UniversalTensorSquare.sg40426`, `OAI.UniversalTensorSquare.sg40428`, `OAI.UniversalTensorSquare.sg40429`, `OAI.UniversalTensorSquare.sg40533`, `OAI.UniversalTensorSquare.sg40537`, `OAI.UniversalTensorSquare.sg40546`, `OAI.UniversalTensorSquare.sg40548`, `OAI.UniversalTensorSquare.sg40549`, `OAI.UniversalTensorSquare.sg41903`, `OAI.UniversalTensorSquare.sg42375`, `OAI.UniversalTensorSquare.sg6768` and `OAI.UniversalTensorSquare.sg6779` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1416)

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

lemma sg1416 : RowSquare [6,3,1,1] [2,2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
