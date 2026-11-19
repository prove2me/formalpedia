-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg6470
-- name    : OAI.UniversalTensorSquare.sg6470
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:01:29.38753+00:00
-- url     : https://prove2.me/theorems/1dd7731b-a776-48a5-9687-1496fa0794cc
-- title:
--   OAI.UniversalTensorSquare.sg6470: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg6470` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg6470 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_320All`, `OAI.UniversalTensorSquare.degreeTree62_444All`, `OAI.UniversalTensorSquare.degreeTree62_456All`, `OAI.UniversalTensorSquare.degreeTree62_462All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_542All`, `OAI.UniversalTensorSquare.degreeTree62_547All`, `OAI.UniversalTensorSquare.degreeTree62_578All`, `OAI.UniversalTensorSquare.degreeTree62_627All`, `OAI.UniversalTensorSquare.degreeTree62_629All`, `OAI.UniversalTensorSquare.degreeTree62_631All`, `OAI.UniversalTensorSquare.degreeTree62_637All`, `OAI.UniversalTensorSquare.degreeTree62_640All`, `OAI.UniversalTensorSquare.degreeTree62_653All`, `OAI.UniversalTensorSquare.sg18913`, `OAI.UniversalTensorSquare.sg34030`, `OAI.UniversalTensorSquare.sg34622`, `OAI.UniversalTensorSquare.sg34645`, `OAI.UniversalTensorSquare.sg34702`, `OAI.UniversalTensorSquare.sg34735`, `OAI.UniversalTensorSquare.sg35503`, `OAI.UniversalTensorSquare.sg35691`, `OAI.UniversalTensorSquare.sg36125`, `OAI.UniversalTensorSquare.sg36133`, `OAI.UniversalTensorSquare.sg36177`, `OAI.UniversalTensorSquare.sg36204`, `OAI.UniversalTensorSquare.sg36291`, `OAI.UniversalTensorSquare.sg36367`, `OAI.UniversalTensorSquare.sg36376`, `OAI.UniversalTensorSquare.sg36387`, `OAI.UniversalTensorSquare.sg36391`, `OAI.UniversalTensorSquare.sg36412`, `OAI.UniversalTensorSquare.sg36433`, `OAI.UniversalTensorSquare.sg36437`, `OAI.UniversalTensorSquare.sg36516`, `OAI.UniversalTensorSquare.sg36542`, `OAI.UniversalTensorSquare.sg36552`, `OAI.UniversalTensorSquare.sg36559`, `OAI.UniversalTensorSquare.sg36627`, `OAI.UniversalTensorSquare.sg36639`, `OAI.UniversalTensorSquare.sg36643`, `OAI.UniversalTensorSquare.sg36654`, `OAI.UniversalTensorSquare.sg36662`, `OAI.UniversalTensorSquare.sg36676`, `OAI.UniversalTensorSquare.sg36683`, `OAI.UniversalTensorSquare.sg36706`, `OAI.UniversalTensorSquare.sg36735`, `OAI.UniversalTensorSquare.sg36758`, `OAI.UniversalTensorSquare.sg36783`, `OAI.UniversalTensorSquare.sg36795`, `OAI.UniversalTensorSquare.sg36922`, `OAI.UniversalTensorSquare.sg36954`, `OAI.UniversalTensorSquare.sg37025`, `OAI.UniversalTensorSquare.sg37079`, `OAI.UniversalTensorSquare.sg37095`, `OAI.UniversalTensorSquare.sg37124`, `OAI.UniversalTensorSquare.sg37131`, `OAI.UniversalTensorSquare.sg37146`, `OAI.UniversalTensorSquare.sg37169`, `OAI.UniversalTensorSquare.sg37179`, `OAI.UniversalTensorSquare.sg37200`, `OAI.UniversalTensorSquare.sg37212`, `OAI.UniversalTensorSquare.sg37231`, `OAI.UniversalTensorSquare.sg37262`, `OAI.UniversalTensorSquare.sg37276`, `OAI.UniversalTensorSquare.sg37320`, `OAI.UniversalTensorSquare.sg37330`, `OAI.UniversalTensorSquare.sg37367`, `OAI.UniversalTensorSquare.sg37380`, `OAI.UniversalTensorSquare.sg37425`, `OAI.UniversalTensorSquare.sg37475`, `OAI.UniversalTensorSquare.sg37626`, `OAI.UniversalTensorSquare.sg37721`, `OAI.UniversalTensorSquare.sg37730`, `OAI.UniversalTensorSquare.sg37752`, `OAI.UniversalTensorSquare.sg37760`, `OAI.UniversalTensorSquare.sg37780`, `OAI.UniversalTensorSquare.sg37791`, `OAI.UniversalTensorSquare.sg37805`, `OAI.UniversalTensorSquare.sg37813`, `OAI.UniversalTensorSquare.sg37825`, `OAI.UniversalTensorSquare.sg37831`, `OAI.UniversalTensorSquare.sg37877`, `OAI.UniversalTensorSquare.sg37897`, `OAI.UniversalTensorSquare.sg37918`, `OAI.UniversalTensorSquare.sg37929`, `OAI.UniversalTensorSquare.sg37985`, `OAI.UniversalTensorSquare.sg38000`, `OAI.UniversalTensorSquare.sg38008`, `OAI.UniversalTensorSquare.sg38027`, `OAI.UniversalTensorSquare.sg38033`, `OAI.UniversalTensorSquare.sg38047`, `OAI.UniversalTensorSquare.sg38067`, `OAI.UniversalTensorSquare.sg38077`, `OAI.UniversalTensorSquare.sg38096`, `OAI.UniversalTensorSquare.sg38153`, `OAI.UniversalTensorSquare.sg38215`, `OAI.UniversalTensorSquare.sg38249`, `OAI.UniversalTensorSquare.sg38347`, `OAI.UniversalTensorSquare.sg38396`, `OAI.UniversalTensorSquare.sg38407`, `OAI.UniversalTensorSquare.sg38417`, `OAI.UniversalTensorSquare.sg38423`, `OAI.UniversalTensorSquare.sg38435`, `OAI.UniversalTensorSquare.sg38446`, `OAI.UniversalTensorSquare.sg38461`, `OAI.UniversalTensorSquare.sg38479`, `OAI.UniversalTensorSquare.sg38522`, `OAI.UniversalTensorSquare.sg38533`, `OAI.UniversalTensorSquare.sg38573`, `OAI.UniversalTensorSquare.sg38711`, `OAI.UniversalTensorSquare.sg38803`, `OAI.UniversalTensorSquare.sg38924`, `OAI.UniversalTensorSquare.sg38932`, `OAI.UniversalTensorSquare.sg38945`, `OAI.UniversalTensorSquare.sg38992`, `OAI.UniversalTensorSquare.sg38995`, `OAI.UniversalTensorSquare.sg39012`, `OAI.UniversalTensorSquare.sg39028`, `OAI.UniversalTensorSquare.sg39062`, `OAI.UniversalTensorSquare.sg39087`, `OAI.UniversalTensorSquare.sg39097`, `OAI.UniversalTensorSquare.sg39111`, `OAI.UniversalTensorSquare.sg39138`, `OAI.UniversalTensorSquare.sg39149`, `OAI.UniversalTensorSquare.sg39188`, `OAI.UniversalTensorSquare.sg39195`, `OAI.UniversalTensorSquare.sg39214`, `OAI.UniversalTensorSquare.sg39230`, `OAI.UniversalTensorSquare.sg39240`, `OAI.UniversalTensorSquare.sg39253` and `OAI.UniversalTensorSquare.sg39543` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean (declaration OAI.UniversalTensorSquare.sg6470)

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

lemma sg6470 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
