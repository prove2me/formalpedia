-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg7454
-- name    : OAI.UniversalTensorSquare.sg7454
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:36:41.63626+00:00
-- url     : https://prove2.me/theorems/fd9a2b08-400d-4294-8529-14c8a3304f97
-- title:
--   OAI.UniversalTensorSquare.sg7454: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg7454` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes17.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes17.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg7454 : RowSquare [6,4,2,2,1,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_309All`, `OAI.UniversalTensorSquare.degreeTree43_314All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_327All`, `OAI.UniversalTensorSquare.degreeTree43_335All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_343All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree43_356All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_377All`, `OAI.UniversalTensorSquare.degreeTree43_378All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_382All`, `OAI.UniversalTensorSquare.degreeTree43_385All`, `OAI.UniversalTensorSquare.degreeTree43_390All`, `OAI.UniversalTensorSquare.degreeTree43_392All`, `OAI.UniversalTensorSquare.degreeTree43_402All`, `OAI.UniversalTensorSquare.degreeTree43_409All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_611All`, `OAI.UniversalTensorSquare.degreeTree43_625All`, `OAI.UniversalTensorSquare.degreeTree43_635All`, `OAI.UniversalTensorSquare.sg27956`, `OAI.UniversalTensorSquare.sg28005`, `OAI.UniversalTensorSquare.sg28042`, `OAI.UniversalTensorSquare.sg28058`, `OAI.UniversalTensorSquare.sg28068`, `OAI.UniversalTensorSquare.sg28083`, `OAI.UniversalTensorSquare.sg28095`, `OAI.UniversalTensorSquare.sg28166`, `OAI.UniversalTensorSquare.sg28173`, `OAI.UniversalTensorSquare.sg28200`, `OAI.UniversalTensorSquare.sg28208`, `OAI.UniversalTensorSquare.sg28237`, `OAI.UniversalTensorSquare.sg28248`, `OAI.UniversalTensorSquare.sg28306`, `OAI.UniversalTensorSquare.sg28326`, `OAI.UniversalTensorSquare.sg28370`, `OAI.UniversalTensorSquare.sg28495`, `OAI.UniversalTensorSquare.sg28504`, `OAI.UniversalTensorSquare.sg28521`, `OAI.UniversalTensorSquare.sg28546`, `OAI.UniversalTensorSquare.sg28558`, `OAI.UniversalTensorSquare.sg28581`, `OAI.UniversalTensorSquare.sg28641`, `OAI.UniversalTensorSquare.sg28688`, `OAI.UniversalTensorSquare.sg28714`, `OAI.UniversalTensorSquare.sg28720`, `OAI.UniversalTensorSquare.sg28768`, `OAI.UniversalTensorSquare.sg28791`, `OAI.UniversalTensorSquare.sg28796`, `OAI.UniversalTensorSquare.sg28896`, `OAI.UniversalTensorSquare.sg28920`, `OAI.UniversalTensorSquare.sg28943`, `OAI.UniversalTensorSquare.sg28948`, `OAI.UniversalTensorSquare.sg28988`, `OAI.UniversalTensorSquare.sg28993`, `OAI.UniversalTensorSquare.sg29008`, `OAI.UniversalTensorSquare.sg29036`, `OAI.UniversalTensorSquare.sg31455`, `OAI.UniversalTensorSquare.sg31674`, `OAI.UniversalTensorSquare.sg31697`, `OAI.UniversalTensorSquare.sg31708`, `OAI.UniversalTensorSquare.sg31720`, `OAI.UniversalTensorSquare.sg31729`, `OAI.UniversalTensorSquare.sg31740`, `OAI.UniversalTensorSquare.sg31746`, `OAI.UniversalTensorSquare.sg31755`, `OAI.UniversalTensorSquare.sg31888` and `OAI.UniversalTensorSquare.sg31895` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes17.lean (declaration OAI.UniversalTensorSquare.sg7454)

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

lemma sg7454 : RowSquare [6,4,2,2,1,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
