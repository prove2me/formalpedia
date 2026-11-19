-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg839
-- name    : OAI.UniversalTensorSquare.sg839
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:39:54.722017+00:00
-- url     : https://prove2.me/theorems/2219cb51-037c-4680-8ea5-abfb824ff44a
-- title:
--   OAI.UniversalTensorSquare.sg839: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg839` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg839 : RowSquare [4,3,1,1,1] [2,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_546All`, `OAI.UniversalTensorSquare.degreeTree62_795All`, `OAI.UniversalTensorSquare.sg34625`, `OAI.UniversalTensorSquare.sg34642`, `OAI.UniversalTensorSquare.sg34644`, `OAI.UniversalTensorSquare.sg34646`, `OAI.UniversalTensorSquare.sg34674`, `OAI.UniversalTensorSquare.sg34684`, `OAI.UniversalTensorSquare.sg34687`, `OAI.UniversalTensorSquare.sg34689`, `OAI.UniversalTensorSquare.sg34782`, `OAI.UniversalTensorSquare.sg34792`, `OAI.UniversalTensorSquare.sg34795`, `OAI.UniversalTensorSquare.sg34797`, `OAI.UniversalTensorSquare.sg35953`, `OAI.UniversalTensorSquare.sg36461`, `OAI.UniversalTensorSquare.sg36463`, `OAI.UniversalTensorSquare.sg36465`, `OAI.UniversalTensorSquare.sg36801`, `OAI.UniversalTensorSquare.sg36803`, `OAI.UniversalTensorSquare.sg37258`, `OAI.UniversalTensorSquare.sg37261`, `OAI.UniversalTensorSquare.sg37263`, `OAI.UniversalTensorSquare.sg37280`, `OAI.UniversalTensorSquare.sg37283`, `OAI.UniversalTensorSquare.sg38020`, `OAI.UniversalTensorSquare.sg38044`, `OAI.UniversalTensorSquare.sg38048`, `OAI.UniversalTensorSquare.sg38139`, `OAI.UniversalTensorSquare.sg38149`, `OAI.UniversalTensorSquare.sg38152`, `OAI.UniversalTensorSquare.sg38154`, `OAI.UniversalTensorSquare.sg38177`, `OAI.UniversalTensorSquare.sg38508`, `OAI.UniversalTensorSquare.sg38518`, `OAI.UniversalTensorSquare.sg38521`, `OAI.UniversalTensorSquare.sg38523`, `OAI.UniversalTensorSquare.sg38591`, `OAI.UniversalTensorSquare.sg38593`, `OAI.UniversalTensorSquare.sg38621`, `OAI.UniversalTensorSquare.sg38631`, `OAI.UniversalTensorSquare.sg38634`, `OAI.UniversalTensorSquare.sg38636`, `OAI.UniversalTensorSquare.sg39021`, `OAI.UniversalTensorSquare.sg39042`, `OAI.UniversalTensorSquare.sg39044`, `OAI.UniversalTensorSquare.sg39046`, `OAI.UniversalTensorSquare.sg39223`, `OAI.UniversalTensorSquare.sg39237`, `OAI.UniversalTensorSquare.sg39239`, `OAI.UniversalTensorSquare.sg39241`, `OAI.UniversalTensorSquare.sg39271`, `OAI.UniversalTensorSquare.sg39285`, `OAI.UniversalTensorSquare.sg39289`, `OAI.UniversalTensorSquare.sg39294`, `OAI.UniversalTensorSquare.sg39304`, `OAI.UniversalTensorSquare.sg39307`, `OAI.UniversalTensorSquare.sg39308`, `OAI.UniversalTensorSquare.sg39539`, `OAI.UniversalTensorSquare.sg39553`, `OAI.UniversalTensorSquare.sg39555`, `OAI.UniversalTensorSquare.sg39556`, `OAI.UniversalTensorSquare.sg39578`, `OAI.UniversalTensorSquare.sg39580`, `OAI.UniversalTensorSquare.sg39581`, `OAI.UniversalTensorSquare.sg40086`, `OAI.UniversalTensorSquare.sg40097`, `OAI.UniversalTensorSquare.sg40099`, `OAI.UniversalTensorSquare.sg40100`, `OAI.UniversalTensorSquare.sg40611`, `OAI.UniversalTensorSquare.sg40622`, `OAI.UniversalTensorSquare.sg40623`, `OAI.UniversalTensorSquare.sg41043`, `OAI.UniversalTensorSquare.sg41052`, `OAI.UniversalTensorSquare.sg41054`, `OAI.UniversalTensorSquare.sg41055`, `OAI.UniversalTensorSquare.sg41562`, `OAI.UniversalTensorSquare.sg41574`, `OAI.UniversalTensorSquare.sg41575`, `OAI.UniversalTensorSquare.sg42207`, `OAI.UniversalTensorSquare.sg42569`, `OAI.UniversalTensorSquare.sg42653`, `OAI.UniversalTensorSquare.sg42809`, `OAI.UniversalTensorSquare.sg42810`, `OAI.UniversalTensorSquare.sg42880`, `OAI.UniversalTensorSquare.sg42881`, `OAI.UniversalTensorSquare.sg42938`, `OAI.UniversalTensorSquare.sg42939`, `OAI.UniversalTensorSquare.sg42953`, `OAI.UniversalTensorSquare.sg42954`, `OAI.UniversalTensorSquare.sg43053`, `OAI.UniversalTensorSquare.sg43054`, `OAI.UniversalTensorSquare.sg43100`, `OAI.UniversalTensorSquare.sg43101`, `OAI.UniversalTensorSquare.sg43111`, `OAI.UniversalTensorSquare.sg43157`, `OAI.UniversalTensorSquare.sg43164`, `OAI.UniversalTensorSquare.sg43177`, `OAI.UniversalTensorSquare.sg5718`, `OAI.UniversalTensorSquare.sg7905`, `OAI.UniversalTensorSquare.sg7907`, `OAI.UniversalTensorSquare.sg7917`, `OAI.UniversalTensorSquare.sg7922`, `OAI.UniversalTensorSquare.sg7923`, `OAI.UniversalTensorSquare.sg7930`, `OAI.UniversalTensorSquare.sg7931`, `OAI.UniversalTensorSquare.sg7948` and `OAI.UniversalTensorSquare.sg7958` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg839)

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

lemma sg839 : RowSquare [4,3,1,1,1] [2,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
