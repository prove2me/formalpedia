-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3523
-- name    : OAI.UniversalTensorSquare.sg3523
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T10:40:05.470568+00:00
-- url     : https://prove2.me/theorems/0e8625ae-467a-4b97-936b-65799648dff9
-- title:
--   OAI.UniversalTensorSquare.sg3523: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3523` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3523 : RowSquare [8,1,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_351All`, `OAI.UniversalTensorSquare.degreeTree62_556All`, `OAI.UniversalTensorSquare.degreeTree62_648All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_726All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.sg20633`, `OAI.UniversalTensorSquare.sg34330`, `OAI.UniversalTensorSquare.sg34339`, `OAI.UniversalTensorSquare.sg34365`, `OAI.UniversalTensorSquare.sg34396`, `OAI.UniversalTensorSquare.sg34511`, `OAI.UniversalTensorSquare.sg34536`, `OAI.UniversalTensorSquare.sg36613`, `OAI.UniversalTensorSquare.sg36620`, `OAI.UniversalTensorSquare.sg36772`, `OAI.UniversalTensorSquare.sg36828`, `OAI.UniversalTensorSquare.sg36845`, `OAI.UniversalTensorSquare.sg36980`, `OAI.UniversalTensorSquare.sg36994`, `OAI.UniversalTensorSquare.sg37001`, `OAI.UniversalTensorSquare.sg37056`, `OAI.UniversalTensorSquare.sg37063`, `OAI.UniversalTensorSquare.sg37908`, `OAI.UniversalTensorSquare.sg37957`, `OAI.UniversalTensorSquare.sg37972`, `OAI.UniversalTensorSquare.sg38135`, `OAI.UniversalTensorSquare.sg38176`, `OAI.UniversalTensorSquare.sg38187`, `OAI.UniversalTensorSquare.sg38193`, `OAI.UniversalTensorSquare.sg38282`, `OAI.UniversalTensorSquare.sg38320`, `OAI.UniversalTensorSquare.sg38328`, `OAI.UniversalTensorSquare.sg38471`, `OAI.UniversalTensorSquare.sg38542`, `OAI.UniversalTensorSquare.sg38553`, `OAI.UniversalTensorSquare.sg38590`, `OAI.UniversalTensorSquare.sg38598`, `OAI.UniversalTensorSquare.sg38655`, `OAI.UniversalTensorSquare.sg38689`, `OAI.UniversalTensorSquare.sg38697`, `OAI.UniversalTensorSquare.sg38722`, `OAI.UniversalTensorSquare.sg38728`, `OAI.UniversalTensorSquare.sg38755`, `OAI.UniversalTensorSquare.sg38820`, `OAI.UniversalTensorSquare.sg38850`, `OAI.UniversalTensorSquare.sg38874`, `OAI.UniversalTensorSquare.sg38895`, `OAI.UniversalTensorSquare.sg39053`, `OAI.UniversalTensorSquare.sg39120`, `OAI.UniversalTensorSquare.sg39167`, `OAI.UniversalTensorSquare.sg39173`, `OAI.UniversalTensorSquare.sg39261`, `OAI.UniversalTensorSquare.sg39325`, `OAI.UniversalTensorSquare.sg39335`, `OAI.UniversalTensorSquare.sg39369`, `OAI.UniversalTensorSquare.sg39376`, `OAI.UniversalTensorSquare.sg39460`, `OAI.UniversalTensorSquare.sg39467`, `OAI.UniversalTensorSquare.sg39495`, `OAI.UniversalTensorSquare.sg39520`, `OAI.UniversalTensorSquare.sg39626`, `OAI.UniversalTensorSquare.sg39702`, `OAI.UniversalTensorSquare.sg39709`, `OAI.UniversalTensorSquare.sg39737`, `OAI.UniversalTensorSquare.sg39794`, `OAI.UniversalTensorSquare.sg39821`, `OAI.UniversalTensorSquare.sg39843`, `OAI.UniversalTensorSquare.sg39863`, `OAI.UniversalTensorSquare.sg39916`, `OAI.UniversalTensorSquare.sg39921`, `OAI.UniversalTensorSquare.sg39938`, `OAI.UniversalTensorSquare.sg39956`, `OAI.UniversalTensorSquare.sg39991`, `OAI.UniversalTensorSquare.sg40035`, `OAI.UniversalTensorSquare.sg40037`, `OAI.UniversalTensorSquare.sg40084`, `OAI.UniversalTensorSquare.sg40103`, `OAI.UniversalTensorSquare.sg40116`, `OAI.UniversalTensorSquare.sg40119`, `OAI.UniversalTensorSquare.sg40135`, `OAI.UniversalTensorSquare.sg40172`, `OAI.UniversalTensorSquare.sg40184`, `OAI.UniversalTensorSquare.sg40206`, `OAI.UniversalTensorSquare.sg40222`, `OAI.UniversalTensorSquare.sg40518`, `OAI.UniversalTensorSquare.sg40904`, `OAI.UniversalTensorSquare.sg40934`, `OAI.UniversalTensorSquare.sg41077` and `OAI.UniversalTensorSquare.sg42668` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3523)

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

lemma sg3523 : RowSquare [8,1,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
