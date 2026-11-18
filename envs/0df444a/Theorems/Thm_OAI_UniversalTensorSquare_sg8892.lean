-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8892
-- name    : OAI.UniversalTensorSquare.sg8892
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:52:46.479463+00:00
-- url     : https://prove2.me/theorems/65a9b754-c38b-42f6-94cd-45f910635bcc
-- title:
--   OAI.UniversalTensorSquare.sg8892: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8892` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8892 : RowSquare [8,4,3,2,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_364All`, `OAI.UniversalTensorSquare.degreeTree62_372All`, `OAI.UniversalTensorSquare.degreeTree62_403All`, `OAI.UniversalTensorSquare.degreeTree62_462All`, `OAI.UniversalTensorSquare.degreeTree62_469All`, `OAI.UniversalTensorSquare.sg19624`, `OAI.UniversalTensorSquare.sg33247`, `OAI.UniversalTensorSquare.sg33505`, `OAI.UniversalTensorSquare.sg35728`, `OAI.UniversalTensorSquare.sg35743`, `OAI.UniversalTensorSquare.sg35783`, `OAI.UniversalTensorSquare.sg35799`, `OAI.UniversalTensorSquare.sg35802`, `OAI.UniversalTensorSquare.sg35856`, `OAI.UniversalTensorSquare.sg35914`, `OAI.UniversalTensorSquare.sg35930`, `OAI.UniversalTensorSquare.sg35946`, `OAI.UniversalTensorSquare.sg35949`, `OAI.UniversalTensorSquare.sg35999`, `OAI.UniversalTensorSquare.sg36056`, `OAI.UniversalTensorSquare.sg36072`, `OAI.UniversalTensorSquare.sg36136`, `OAI.UniversalTensorSquare.sg36139`, `OAI.UniversalTensorSquare.sg36157`, `OAI.UniversalTensorSquare.sg36182`, `OAI.UniversalTensorSquare.sg36207`, `OAI.UniversalTensorSquare.sg36221`, `OAI.UniversalTensorSquare.sg36246`, `OAI.UniversalTensorSquare.sg36394`, `OAI.UniversalTensorSquare.sg36456`, `OAI.UniversalTensorSquare.sg36459`, `OAI.UniversalTensorSquare.sg36486`, `OAI.UniversalTensorSquare.sg36508`, `OAI.UniversalTensorSquare.sg36528`, `OAI.UniversalTensorSquare.sg36555`, `OAI.UniversalTensorSquare.sg36564`, `OAI.UniversalTensorSquare.sg36580`, `OAI.UniversalTensorSquare.sg36630`, `OAI.UniversalTensorSquare.sg36646`, `OAI.UniversalTensorSquare.sg36668`, `OAI.UniversalTensorSquare.sg36720`, `OAI.UniversalTensorSquare.sg36738`, `OAI.UniversalTensorSquare.sg36747`, `OAI.UniversalTensorSquare.sg36763`, `OAI.UniversalTensorSquare.sg36768`, `OAI.UniversalTensorSquare.sg36786`, `OAI.UniversalTensorSquare.sg36800`, `OAI.UniversalTensorSquare.sg36824`, `OAI.UniversalTensorSquare.sg36880`, `OAI.UniversalTensorSquare.sg36893`, `OAI.UniversalTensorSquare.sg36907`, `OAI.UniversalTensorSquare.sg36960`, `OAI.UniversalTensorSquare.sg37086`, `OAI.UniversalTensorSquare.sg37106`, `OAI.UniversalTensorSquare.sg37136`, `OAI.UniversalTensorSquare.sg37151`, `OAI.UniversalTensorSquare.sg37191`, `OAI.UniversalTensorSquare.sg37203`, `OAI.UniversalTensorSquare.sg37222`, `OAI.UniversalTensorSquare.sg37240`, `OAI.UniversalTensorSquare.sg37268` and `OAI.UniversalTensorSquare.sg37347` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean (declaration OAI.UniversalTensorSquare.sg8892)

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

lemma sg8892 : RowSquare [8,4,3,2,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
