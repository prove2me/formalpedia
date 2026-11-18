-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg18911
-- name    : OAI.UniversalTensorSquare.sg18911
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T09:10:32.601086+00:00
-- url     : https://prove2.me/theorems/1f921b56-83a1-4e77-b467-714f0e7a0eb5
-- title:
--   OAI.UniversalTensorSquare.sg18911: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg18911` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes45.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes45.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg18911 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_629All`, `OAI.UniversalTensorSquare.degreeTree62_640All`, `OAI.UniversalTensorSquare.degreeTree62_653All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_726All`, `OAI.UniversalTensorSquare.degreeTree62_738All`, `OAI.UniversalTensorSquare.sg33875`, `OAI.UniversalTensorSquare.sg34027`, `OAI.UniversalTensorSquare.sg34292`, `OAI.UniversalTensorSquare.sg34313`, `OAI.UniversalTensorSquare.sg34643`, `OAI.UniversalTensorSquare.sg34685`, `OAI.UniversalTensorSquare.sg34699`, `OAI.UniversalTensorSquare.sg34732`, `OAI.UniversalTensorSquare.sg35628`, `OAI.UniversalTensorSquare.sg35804`, `OAI.UniversalTensorSquare.sg36012`, `OAI.UniversalTensorSquare.sg36049`, `OAI.UniversalTensorSquare.sg36175`, `OAI.UniversalTensorSquare.sg36214`, `OAI.UniversalTensorSquare.sg36288`, `OAI.UniversalTensorSquare.sg36557`, `OAI.UniversalTensorSquare.sg36681`, `OAI.UniversalTensorSquare.sg36756`, `OAI.UniversalTensorSquare.sg36793`, `OAI.UniversalTensorSquare.sg36919`, `OAI.UniversalTensorSquare.sg36951`, `OAI.UniversalTensorSquare.sg37022`, `OAI.UniversalTensorSquare.sg37129`, `OAI.UniversalTensorSquare.sg37144`, `OAI.UniversalTensorSquare.sg37210`, `OAI.UniversalTensorSquare.sg37228`, `OAI.UniversalTensorSquare.sg37259`, `OAI.UniversalTensorSquare.sg37273`, `OAI.UniversalTensorSquare.sg37364`, `OAI.UniversalTensorSquare.sg37377`, `OAI.UniversalTensorSquare.sg37422`, `OAI.UniversalTensorSquare.sg37472`, `OAI.UniversalTensorSquare.sg37623`, `OAI.UniversalTensorSquare.sg37829`, `OAI.UniversalTensorSquare.sg37895`, `OAI.UniversalTensorSquare.sg38031`, `OAI.UniversalTensorSquare.sg38045`, `OAI.UniversalTensorSquare.sg38121`, `OAI.UniversalTensorSquare.sg38150`, `OAI.UniversalTensorSquare.sg38246`, `OAI.UniversalTensorSquare.sg38344`, `OAI.UniversalTensorSquare.sg38421`, `OAI.UniversalTensorSquare.sg38444`, `OAI.UniversalTensorSquare.sg38458`, `OAI.UniversalTensorSquare.sg38519`, `OAI.UniversalTensorSquare.sg38530`, `OAI.UniversalTensorSquare.sg38570`, `OAI.UniversalTensorSquare.sg38669`, `OAI.UniversalTensorSquare.sg38708`, `OAI.UniversalTensorSquare.sg38800`, `OAI.UniversalTensorSquare.sg39095`, `OAI.UniversalTensorSquare.sg39108`, `OAI.UniversalTensorSquare.sg39135`, `OAI.UniversalTensorSquare.sg39146`, `OAI.UniversalTensorSquare.sg39238`, `OAI.UniversalTensorSquare.sg39250`, `OAI.UniversalTensorSquare.sg39305`, `OAI.UniversalTensorSquare.sg39315`, `OAI.UniversalTensorSquare.sg39352`, `OAI.UniversalTensorSquare.sg39419`, `OAI.UniversalTensorSquare.sg39443`, `OAI.UniversalTensorSquare.sg39478`, `OAI.UniversalTensorSquare.sg39606`, `OAI.UniversalTensorSquare.sg39685`, `OAI.UniversalTensorSquare.sg39720`, `OAI.UniversalTensorSquare.sg39804`, `OAI.UniversalTensorSquare.sg39889`, `OAI.UniversalTensorSquare.sg39904`, `OAI.UniversalTensorSquare.sg40109` and `OAI.UniversalTensorSquare.sg40140` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes45.lean (declaration OAI.UniversalTensorSquare.sg18911)

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

lemma sg18911 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
