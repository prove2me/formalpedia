-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg313
-- name    : OAI.UniversalTensorSquare.sg313
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-16T23:59:00.290745+00:00
-- url     : https://prove2.me/theorems/82af8d83-3906-477c-9a51-bcb1a6485395
-- title:
--   OAI.UniversalTensorSquare.sg313: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg313` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg313 : RowSquare [4,1,1,1,1] [2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_110All`, `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_264All`, `OAI.UniversalTensorSquare.degreeTree43_473All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_583All`, `OAI.UniversalTensorSquare.degreeTree43_618All`, `OAI.UniversalTensorSquare.degreeTree43_82All`, `OAI.UniversalTensorSquare.degreeTree62_155All`, `OAI.UniversalTensorSquare.degreeTree62_19All`, `OAI.UniversalTensorSquare.degreeTree62_530All`, `OAI.UniversalTensorSquare.degreeTree62_534All`, `OAI.UniversalTensorSquare.degreeTree62_549All`, `OAI.UniversalTensorSquare.degreeTree62_617All`, `OAI.UniversalTensorSquare.degreeTree62_641All`, `OAI.UniversalTensorSquare.degreeTree62_661All`, `OAI.UniversalTensorSquare.degreeTree62_672All`, `OAI.UniversalTensorSquare.degreeTree62_717All`, `OAI.UniversalTensorSquare.degreeTree62_733All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_869All`, `OAI.UniversalTensorSquare.degreeTree62_955All`, `OAI.UniversalTensorSquare.sg22495`, `OAI.UniversalTensorSquare.sg22646`, `OAI.UniversalTensorSquare.sg22648`, `OAI.UniversalTensorSquare.sg24207`, `OAI.UniversalTensorSquare.sg24519`, `OAI.UniversalTensorSquare.sg24573`, `OAI.UniversalTensorSquare.sg24616`, `OAI.UniversalTensorSquare.sg24625`, `OAI.UniversalTensorSquare.sg24646`, `OAI.UniversalTensorSquare.sg24664`, `OAI.UniversalTensorSquare.sg24892`, `OAI.UniversalTensorSquare.sg24930`, `OAI.UniversalTensorSquare.sg24955`, `OAI.UniversalTensorSquare.sg24988`, `OAI.UniversalTensorSquare.sg25012`, `OAI.UniversalTensorSquare.sg25040`, `OAI.UniversalTensorSquare.sg25870`, `OAI.UniversalTensorSquare.sg26273`, `OAI.UniversalTensorSquare.sg26527`, `OAI.UniversalTensorSquare.sg26531`, `OAI.UniversalTensorSquare.sg26533`, `OAI.UniversalTensorSquare.sg27213`, `OAI.UniversalTensorSquare.sg27445`, `OAI.UniversalTensorSquare.sg28605`, `OAI.UniversalTensorSquare.sg28611`, `OAI.UniversalTensorSquare.sg28741`, `OAI.UniversalTensorSquare.sg28744`, `OAI.UniversalTensorSquare.sg28826`, `OAI.UniversalTensorSquare.sg28833`, `OAI.UniversalTensorSquare.sg28836`, `OAI.UniversalTensorSquare.sg29757`, `OAI.UniversalTensorSquare.sg30277`, `OAI.UniversalTensorSquare.sg36549`, `OAI.UniversalTensorSquare.sg38100`, `OAI.UniversalTensorSquare.sg39312`, `OAI.UniversalTensorSquare.sg39315`, `OAI.UniversalTensorSquare.sg7780` and `OAI.UniversalTensorSquare.sg9217` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sg313)

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

lemma sg313 : RowSquare [4,1,1,1,1] [2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
