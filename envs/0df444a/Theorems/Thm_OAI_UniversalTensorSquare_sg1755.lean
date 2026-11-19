-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1755
-- name    : OAI.UniversalTensorSquare.sg1755
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:09:40.315166+00:00
-- url     : https://prove2.me/theorems/0145042c-90d6-4645-b172-8d18a2bad0bd
-- title:
--   OAI.UniversalTensorSquare.sg1755: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1755` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_285All`, `OAI.UniversalTensorSquare.degreeTree43_378All`, `OAI.UniversalTensorSquare.degreeTree62_146All`, `OAI.UniversalTensorSquare.degreeTree62_444All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_634All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_723All`, `OAI.UniversalTensorSquare.degreeTree62_727All`, `OAI.UniversalTensorSquare.degreeTree62_738All`, `OAI.UniversalTensorSquare.degreeTree62_746All`, `OAI.UniversalTensorSquare.degreeTree62_872All`, `OAI.UniversalTensorSquare.degreeTree62_937All`, `OAI.UniversalTensorSquare.degreeTree62_956All`, `OAI.UniversalTensorSquare.degreeTree62_973All`, `OAI.UniversalTensorSquare.degreeTreeAll39`, `OAI.UniversalTensorSquare.sg18915`, `OAI.UniversalTensorSquare.sg34323`, `OAI.UniversalTensorSquare.sg34336`, `OAI.UniversalTensorSquare.sg34351`, `OAI.UniversalTensorSquare.sg34362`, `OAI.UniversalTensorSquare.sg34389`, `OAI.UniversalTensorSquare.sg34393`, `OAI.UniversalTensorSquare.sg35730`, `OAI.UniversalTensorSquare.sg36381`, `OAI.UniversalTensorSquare.sg36570`, `OAI.UniversalTensorSquare.sg36633`, `OAI.UniversalTensorSquare.sg36753`, `OAI.UniversalTensorSquare.sg36947`, `OAI.UniversalTensorSquare.sg37785`, `OAI.UniversalTensorSquare.sg37892`, `OAI.UniversalTensorSquare.sg37979`, `OAI.UniversalTensorSquare.sg38042`, `OAI.UniversalTensorSquare.sg38102`, `OAI.UniversalTensorSquare.sg38221`, `OAI.UniversalTensorSquare.sg38242`, `OAI.UniversalTensorSquare.sg38441`, `OAI.UniversalTensorSquare.sg38495`, `OAI.UniversalTensorSquare.sg38515`, `OAI.UniversalTensorSquare.sg38694`, `OAI.UniversalTensorSquare.sg38752`, `OAI.UniversalTensorSquare.sg38847`, `OAI.UniversalTensorSquare.sg38871`, `OAI.UniversalTensorSquare.sg38892`, `OAI.UniversalTensorSquare.sg38986`, `OAI.UniversalTensorSquare.sg39040`, `OAI.UniversalTensorSquare.sg39092`, `OAI.UniversalTensorSquare.sg39131`, `OAI.UniversalTensorSquare.sg39235`, `OAI.UniversalTensorSquare.sg39465`, `OAI.UniversalTensorSquare.sg39493`, `OAI.UniversalTensorSquare.sg39518`, `OAI.UniversalTensorSquare.sg39593`, `OAI.UniversalTensorSquare.sg39649`, `OAI.UniversalTensorSquare.sg39707`, `OAI.UniversalTensorSquare.sg39757`, `OAI.UniversalTensorSquare.sg39861`, `OAI.UniversalTensorSquare.sg39919`, `OAI.UniversalTensorSquare.sg39936`, `OAI.UniversalTensorSquare.sg39954`, `OAI.UniversalTensorSquare.sg40040`, `OAI.UniversalTensorSquare.sg40114`, `OAI.UniversalTensorSquare.sg40138`, `OAI.UniversalTensorSquare.sg40170`, `OAI.UniversalTensorSquare.sg40385`, `OAI.UniversalTensorSquare.sg40412`, `OAI.UniversalTensorSquare.sg40494`, `OAI.UniversalTensorSquare.sg40829`, `OAI.UniversalTensorSquare.sg40896`, `OAI.UniversalTensorSquare.sg40915`, `OAI.UniversalTensorSquare.sg40946`, `OAI.UniversalTensorSquare.sg40987`, `OAI.UniversalTensorSquare.sg41023`, `OAI.UniversalTensorSquare.sg41050`, `OAI.UniversalTensorSquare.sg41095`, `OAI.UniversalTensorSquare.sg41514`, `OAI.UniversalTensorSquare.sg41541`, `OAI.UniversalTensorSquare.sg41601`, `OAI.UniversalTensorSquare.sg41681`, `OAI.UniversalTensorSquare.sg41707`, `OAI.UniversalTensorSquare.sg41717`, `OAI.UniversalTensorSquare.sg41777`, `OAI.UniversalTensorSquare.sg41869`, `OAI.UniversalTensorSquare.sg42023`, `OAI.UniversalTensorSquare.sg42497`, `OAI.UniversalTensorSquare.sg42760`, `OAI.UniversalTensorSquare.sg42770`, `OAI.UniversalTensorSquare.sg4837` and `OAI.UniversalTensorSquare.sg9455` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean (declaration OAI.UniversalTensorSquare.sg1755)

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

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
