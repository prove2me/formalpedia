-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20852
-- name    : OAI.UniversalTensorSquare.sg20852
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:14:01.130659+00:00
-- url     : https://prove2.me/theorems/53298924-73a9-4580-a478-908bdfac235a
-- title:
--   OAI.UniversalTensorSquare.sg20852: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20852` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20852 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_547All`, `OAI.UniversalTensorSquare.degreeTree62_727All`, `OAI.UniversalTensorSquare.degreeTree62_738All`, `OAI.UniversalTensorSquare.degreeTree62_871All`, `OAI.UniversalTensorSquare.degreeTree62_932All`, `OAI.UniversalTensorSquare.sg33757`, `OAI.UniversalTensorSquare.sg33924`, `OAI.UniversalTensorSquare.sg33966`, `OAI.UniversalTensorSquare.sg34161`, `OAI.UniversalTensorSquare.sg34203`, `OAI.UniversalTensorSquare.sg34245`, `OAI.UniversalTensorSquare.sg34284`, `OAI.UniversalTensorSquare.sg34320`, `OAI.UniversalTensorSquare.sg34498`, `OAI.UniversalTensorSquare.sg34530`, `OAI.UniversalTensorSquare.sg35489`, `OAI.UniversalTensorSquare.sg35680`, `OAI.UniversalTensorSquare.sg35723`, `OAI.UniversalTensorSquare.sg35768`, `OAI.UniversalTensorSquare.sg36425`, `OAI.UniversalTensorSquare.sg36471`, `OAI.UniversalTensorSquare.sg36487`, `OAI.UniversalTensorSquare.sg36540`, `OAI.UniversalTensorSquare.sg36631`, `OAI.UniversalTensorSquare.sg36647`, `OAI.UniversalTensorSquare.sg36699`, `OAI.UniversalTensorSquare.sg36723`, `OAI.UniversalTensorSquare.sg36856`, `OAI.UniversalTensorSquare.sg37014`, `OAI.UniversalTensorSquare.sg37733`, `OAI.UniversalTensorSquare.sg37783`, `OAI.UniversalTensorSquare.sg37798`, `OAI.UniversalTensorSquare.sg37843`, `OAI.UniversalTensorSquare.sg37977`, `OAI.UniversalTensorSquare.sg37993`, `OAI.UniversalTensorSquare.sg38065`, `OAI.UniversalTensorSquare.sg38236`, `OAI.UniversalTensorSquare.sg38381`, `OAI.UniversalTensorSquare.sg38405`, `OAI.UniversalTensorSquare.sg38562`, `OAI.UniversalTensorSquare.sg38661`, `OAI.UniversalTensorSquare.sg38792`, `OAI.UniversalTensorSquare.sg38934`, `OAI.UniversalTensorSquare.sg38947`, `OAI.UniversalTensorSquare.sg38984`, `OAI.UniversalTensorSquare.sg38998`, `OAI.UniversalTensorSquare.sg39017`, `OAI.UniversalTensorSquare.sg39060`, `OAI.UniversalTensorSquare.sg39181`, `OAI.UniversalTensorSquare.sg39203`, `OAI.UniversalTensorSquare.sg39295`, `OAI.UniversalTensorSquare.sg39344`, `OAI.UniversalTensorSquare.sg39399`, `OAI.UniversalTensorSquare.sg39435`, `OAI.UniversalTensorSquare.sg39541`, `OAI.UniversalTensorSquare.sg39587`, `OAI.UniversalTensorSquare.sg39643`, `OAI.UniversalTensorSquare.sg39678`, `OAI.UniversalTensorSquare.sg39770`, `OAI.UniversalTensorSquare.sg39858`, `OAI.UniversalTensorSquare.sg39882`, `OAI.UniversalTensorSquare.sg39951`, `OAI.UniversalTensorSquare.sg40006`, `OAI.UniversalTensorSquare.sg40021`, `OAI.UniversalTensorSquare.sg40053`, `OAI.UniversalTensorSquare.sg40095`, `OAI.UniversalTensorSquare.sg40193`, `OAI.UniversalTensorSquare.sg40209`, `OAI.UniversalTensorSquare.sg40381`, `OAI.UniversalTensorSquare.sg40410`, `OAI.UniversalTensorSquare.sg40436`, `OAI.UniversalTensorSquare.sg40446`, `OAI.UniversalTensorSquare.sg40476`, `OAI.UniversalTensorSquare.sg40796`, `OAI.UniversalTensorSquare.sg40827`, `OAI.UniversalTensorSquare.sg40837`, `OAI.UniversalTensorSquare.sg40879`, `OAI.UniversalTensorSquare.sg40944`, `OAI.UniversalTensorSquare.sg40955`, `OAI.UniversalTensorSquare.sg40970`, `OAI.UniversalTensorSquare.sg40999`, `OAI.UniversalTensorSquare.sg41044`, `OAI.UniversalTensorSquare.sg41102`, `OAI.UniversalTensorSquare.sg41137`, `OAI.UniversalTensorSquare.sg41512`, `OAI.UniversalTensorSquare.sg41520`, `OAI.UniversalTensorSquare.sg41539`, `OAI.UniversalTensorSquare.sg41548`, `OAI.UniversalTensorSquare.sg41560`, `OAI.UniversalTensorSquare.sg41582`, `OAI.UniversalTensorSquare.sg41617`, `OAI.UniversalTensorSquare.sg41662`, `OAI.UniversalTensorSquare.sg41711`, `OAI.UniversalTensorSquare.sg41740`, `OAI.UniversalTensorSquare.sg41771`, `OAI.UniversalTensorSquare.sg41794`, `OAI.UniversalTensorSquare.sg41849`, `OAI.UniversalTensorSquare.sg41872`, `OAI.UniversalTensorSquare.sg41905`, `OAI.UniversalTensorSquare.sg41927`, `OAI.UniversalTensorSquare.sg41964`, `OAI.UniversalTensorSquare.sg41978`, `OAI.UniversalTensorSquare.sg42024`, `OAI.UniversalTensorSquare.sg42037`, `OAI.UniversalTensorSquare.sg42074`, `OAI.UniversalTensorSquare.sg42092`, `OAI.UniversalTensorSquare.sg42098`, `OAI.UniversalTensorSquare.sg42106`, `OAI.UniversalTensorSquare.sg42118`, `OAI.UniversalTensorSquare.sg42127`, `OAI.UniversalTensorSquare.sg42162`, `OAI.UniversalTensorSquare.sg42187` and `OAI.UniversalTensorSquare.sg42209` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean (declaration OAI.UniversalTensorSquare.sg20852)

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

lemma sg20852 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
