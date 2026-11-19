-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4834
-- name    : OAI.UniversalTensorSquare.sg4834
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:35:28.756271+00:00
-- url     : https://prove2.me/theorems/fffe6dba-b147-4157-b3c2-d9e394808cc5
-- title:
--   OAI.UniversalTensorSquare.sg4834: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4834` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4834 : RowSquare [6,3,2,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_574All`, `OAI.UniversalTensorSquare.degreeTree62_627All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_827All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.degreeTree62_924All`, `OAI.UniversalTensorSquare.degreeTree62_937All`, `OAI.UniversalTensorSquare.degreeTree62_939All`, `OAI.UniversalTensorSquare.degreeTree62_941All`, `OAI.UniversalTensorSquare.degreeTree62_958All`, `OAI.UniversalTensorSquare.degreeTree62_95All`, `OAI.UniversalTensorSquare.degreeTree62_974All`, `OAI.UniversalTensorSquare.sg20505`, `OAI.UniversalTensorSquare.sg20525`, `OAI.UniversalTensorSquare.sg32780`, `OAI.UniversalTensorSquare.sg32797`, `OAI.UniversalTensorSquare.sg32851`, `OAI.UniversalTensorSquare.sg32857`, `OAI.UniversalTensorSquare.sg33672`, `OAI.UniversalTensorSquare.sg34021`, `OAI.UniversalTensorSquare.sg34360`, `OAI.UniversalTensorSquare.sg34446`, `OAI.UniversalTensorSquare.sg34467`, `OAI.UniversalTensorSquare.sg34609`, `OAI.UniversalTensorSquare.sg34693`, `OAI.UniversalTensorSquare.sg34746`, `OAI.UniversalTensorSquare.sg34850`, `OAI.UniversalTensorSquare.sg34913`, `OAI.UniversalTensorSquare.sg34921`, `OAI.UniversalTensorSquare.sg34975`, `OAI.UniversalTensorSquare.sg34999`, `OAI.UniversalTensorSquare.sg35028`, `OAI.UniversalTensorSquare.sg35159`, `OAI.UniversalTensorSquare.sg35261`, `OAI.UniversalTensorSquare.sg35362`, `OAI.UniversalTensorSquare.sg35402`, `OAI.UniversalTensorSquare.sg35423`, `OAI.UniversalTensorSquare.sg35825`, `OAI.UniversalTensorSquare.sg36497`, `OAI.UniversalTensorSquare.sg36778`, `OAI.UniversalTensorSquare.sg37325`, `OAI.UniversalTensorSquare.sg37413`, `OAI.UniversalTensorSquare.sg37466`, `OAI.UniversalTensorSquare.sg37662`, `OAI.UniversalTensorSquare.sg37808`, `OAI.UniversalTensorSquare.sg37913`, `OAI.UniversalTensorSquare.sg38430`, `OAI.UniversalTensorSquare.sg38561`, `OAI.UniversalTensorSquare.sg38702`, `OAI.UniversalTensorSquare.sg39225`, `OAI.UniversalTensorSquare.sg39343`, `OAI.UniversalTensorSquare.sg39472`, `OAI.UniversalTensorSquare.sg39714`, `OAI.UniversalTensorSquare.sg39798`, `OAI.UniversalTensorSquare.sg39832`, `OAI.UniversalTensorSquare.sg39927`, `OAI.UniversalTensorSquare.sg40545`, `OAI.UniversalTensorSquare.sg40613`, `OAI.UniversalTensorSquare.sg40751`, `OAI.UniversalTensorSquare.sg40844`, `OAI.UniversalTensorSquare.sg41015`, `OAI.UniversalTensorSquare.sg41218`, `OAI.UniversalTensorSquare.sg41296`, `OAI.UniversalTensorSquare.sg41358`, `OAI.UniversalTensorSquare.sg41526`, `OAI.UniversalTensorSquare.sg41674`, `OAI.UniversalTensorSquare.sg41700`, `OAI.UniversalTensorSquare.sg41739`, `OAI.UniversalTensorSquare.sg41832`, `OAI.UniversalTensorSquare.sg41863`, `OAI.UniversalTensorSquare.sg41945`, `OAI.UniversalTensorSquare.sg41977`, `OAI.UniversalTensorSquare.sg42011`, `OAI.UniversalTensorSquare.sg42135`, `OAI.UniversalTensorSquare.sg42271`, `OAI.UniversalTensorSquare.sg42287`, `OAI.UniversalTensorSquare.sg42421`, `OAI.UniversalTensorSquare.sg42434`, `OAI.UniversalTensorSquare.sg42450`, `OAI.UniversalTensorSquare.sg42487`, `OAI.UniversalTensorSquare.sg42514`, `OAI.UniversalTensorSquare.sg42525`, `OAI.UniversalTensorSquare.sg42558`, `OAI.UniversalTensorSquare.sg42630`, `OAI.UniversalTensorSquare.sg43013` and `OAI.UniversalTensorSquare.sg43183` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes10.lean (declaration OAI.UniversalTensorSquare.sg4834)

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

lemma sg4834 : RowSquare [6,3,2,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
