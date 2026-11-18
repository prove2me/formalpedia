-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2708
-- name    : OAI.UniversalTensorSquare.sg2708
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T09:17:31.251245+00:00
-- url     : https://prove2.me/theorems/b44d54a1-206c-4b99-a181-097545898e52
-- title:
--   OAI.UniversalTensorSquare.sg2708: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2708` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2708 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_332All`, `OAI.UniversalTensorSquare.degreeTree62_351All`, `OAI.UniversalTensorSquare.degreeTree62_629All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.sg20525`, `OAI.UniversalTensorSquare.sg32644`, `OAI.UniversalTensorSquare.sg32749`, `OAI.UniversalTensorSquare.sg32857`, `OAI.UniversalTensorSquare.sg33672`, `OAI.UniversalTensorSquare.sg34268`, `OAI.UniversalTensorSquare.sg34417`, `OAI.UniversalTensorSquare.sg34454`, `OAI.UniversalTensorSquare.sg34557`, `OAI.UniversalTensorSquare.sg35085`, `OAI.UniversalTensorSquare.sg35365`, `OAI.UniversalTensorSquare.sg35528`, `OAI.UniversalTensorSquare.sg35530`, `OAI.UniversalTensorSquare.sg35574`, `OAI.UniversalTensorSquare.sg35576`, `OAI.UniversalTensorSquare.sg35620`, `OAI.UniversalTensorSquare.sg35622`, `OAI.UniversalTensorSquare.sg35625`, `OAI.UniversalTensorSquare.sg35626`, `OAI.UniversalTensorSquare.sg35657`, `OAI.UniversalTensorSquare.sg35658`, `OAI.UniversalTensorSquare.sg35691`, `OAI.UniversalTensorSquare.sg35693`, `OAI.UniversalTensorSquare.sg35740`, `OAI.UniversalTensorSquare.sg35742`, `OAI.UniversalTensorSquare.sg35743`, `OAI.UniversalTensorSquare.sg35844`, `OAI.UniversalTensorSquare.sg35846`, `OAI.UniversalTensorSquare.sg35856`, `OAI.UniversalTensorSquare.sg35879`, `OAI.UniversalTensorSquare.sg35880`, `OAI.UniversalTensorSquare.sg36044`, `OAI.UniversalTensorSquare.sg36046`, `OAI.UniversalTensorSquare.sg36072`, `OAI.UniversalTensorSquare.sg36182`, `OAI.UniversalTensorSquare.sg36221`, `OAI.UniversalTensorSquare.sg36357`, `OAI.UniversalTensorSquare.sg36391`, `OAI.UniversalTensorSquare.sg36393`, `OAI.UniversalTensorSquare.sg36394`, `OAI.UniversalTensorSquare.sg36459`, `OAI.UniversalTensorSquare.sg36516`, `OAI.UniversalTensorSquare.sg36518`, `OAI.UniversalTensorSquare.sg36528`, `OAI.UniversalTensorSquare.sg36552`, `OAI.UniversalTensorSquare.sg36554`, `OAI.UniversalTensorSquare.sg36580`, `OAI.UniversalTensorSquare.sg36587`, `OAI.UniversalTensorSquare.sg36611`, `OAI.UniversalTensorSquare.sg36676`, `OAI.UniversalTensorSquare.sg36763`, `OAI.UniversalTensorSquare.sg36770`, `OAI.UniversalTensorSquare.sg36800`, `OAI.UniversalTensorSquare.sg36826`, `OAI.UniversalTensorSquare.sg36933`, `OAI.UniversalTensorSquare.sg37069`, `OAI.UniversalTensorSquare.sg37151`, `OAI.UniversalTensorSquare.sg37760`, `OAI.UniversalTensorSquare.sg37762`, `OAI.UniversalTensorSquare.sg37825` and `OAI.UniversalTensorSquare.sg37827` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2708)

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

lemma sg2708 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
