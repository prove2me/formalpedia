-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2596
-- name    : OAI.UniversalTensorSquare.sg2596
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T04:20:34.985211+00:00
-- url     : https://prove2.me/theorems/a897ed05-e8de-489e-b196-ca3a845ffe2e
-- title:
--   OAI.UniversalTensorSquare.sg2596: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2596` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2596 : RowSquare [5,4,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_10All`, `OAI.UniversalTensorSquare.degreeTree26_33All`, `OAI.UniversalTensorSquare.degreeTree26_46All`, `OAI.UniversalTensorSquare.degreeTree26_53All`, `OAI.UniversalTensorSquare.degreeTree26_56All`, `OAI.UniversalTensorSquare.degreeTree26_57All`, `OAI.UniversalTensorSquare.degreeTree26_60All`, `OAI.UniversalTensorSquare.degreeTree26_6All`, `OAI.UniversalTensorSquare.degreeTree35_10All`, `OAI.UniversalTensorSquare.degreeTree35_14All`, `OAI.UniversalTensorSquare.degreeTree35_16All`, `OAI.UniversalTensorSquare.degreeTree35_18All`, `OAI.UniversalTensorSquare.degreeTree35_23All`, `OAI.UniversalTensorSquare.degreeTree35_7All`, `OAI.UniversalTensorSquare.degreeTree35_8All`, `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree39_51All`, `OAI.UniversalTensorSquare.degreeTree39_54All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_66All`, `OAI.UniversalTensorSquare.degreeTree39_81All`, `OAI.UniversalTensorSquare.degreeTree41_11All`, `OAI.UniversalTensorSquare.degreeTree41_12All`, `OAI.UniversalTensorSquare.degreeTree43_116All`, `OAI.UniversalTensorSquare.degreeTree43_309All`, `OAI.UniversalTensorSquare.degreeTree43_314All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_327All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.sg11890`, `OAI.UniversalTensorSquare.sg11910`, `OAI.UniversalTensorSquare.sg11916`, `OAI.UniversalTensorSquare.sg11956`, `OAI.UniversalTensorSquare.sg12063`, `OAI.UniversalTensorSquare.sg12069`, `OAI.UniversalTensorSquare.sg12086`, `OAI.UniversalTensorSquare.sg12121`, `OAI.UniversalTensorSquare.sg12192`, `OAI.UniversalTensorSquare.sg12199`, `OAI.UniversalTensorSquare.sg12217`, `OAI.UniversalTensorSquare.sg12271`, `OAI.UniversalTensorSquare.sg12277`, `OAI.UniversalTensorSquare.sg12308`, `OAI.UniversalTensorSquare.sg12323`, `OAI.UniversalTensorSquare.sg21437`, `OAI.UniversalTensorSquare.sg21461`, `OAI.UniversalTensorSquare.sg21466`, `OAI.UniversalTensorSquare.sg21477`, `OAI.UniversalTensorSquare.sg21481`, `OAI.UniversalTensorSquare.sg21490`, `OAI.UniversalTensorSquare.sg21505`, `OAI.UniversalTensorSquare.sg21516`, `OAI.UniversalTensorSquare.sg22489`, `OAI.UniversalTensorSquare.sg22541`, `OAI.UniversalTensorSquare.sg22586`, `OAI.UniversalTensorSquare.sg22764`, `OAI.UniversalTensorSquare.sg22771`, `OAI.UniversalTensorSquare.sg22778`, `OAI.UniversalTensorSquare.sg22787`, `OAI.UniversalTensorSquare.sg22800`, `OAI.UniversalTensorSquare.sg22811`, `OAI.UniversalTensorSquare.sg22823`, `OAI.UniversalTensorSquare.sg22857`, `OAI.UniversalTensorSquare.sg22867`, `OAI.UniversalTensorSquare.sg22882`, `OAI.UniversalTensorSquare.sg22943`, `OAI.UniversalTensorSquare.sg23400`, `OAI.UniversalTensorSquare.sg23508`, `OAI.UniversalTensorSquare.sg25129`, `OAI.UniversalTensorSquare.sg27859`, `OAI.UniversalTensorSquare.sg27958`, `OAI.UniversalTensorSquare.sg28007`, `OAI.UniversalTensorSquare.sg28015`, `OAI.UniversalTensorSquare.sg28044`, `OAI.UniversalTensorSquare.sg4797` and `OAI.UniversalTensorSquare.sg5515` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg2596)

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

lemma sg2596 : RowSquare [5,4,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
