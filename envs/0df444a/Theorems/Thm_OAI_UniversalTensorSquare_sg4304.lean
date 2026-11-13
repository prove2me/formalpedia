-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4304
-- name    : OAI.UniversalTensorSquare.sg4304
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T21:35:36.782659+00:00
-- url     : https://prove2.me/theorems/59cbe0ca-06f2-4a7c-88c2-632db054dc8b
-- title:
--   OAI.UniversalTensorSquare.sg4304: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4304` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4304 : RowSquare [7,4,2,1,1,1] [3,3,3,3,3,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_28All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.degreeTree62_390All`, `OAI.UniversalTensorSquare.degreeTree62_4All`, `OAI.UniversalTensorSquare.degreeTree62_80All`, `OAI.UniversalTensorSquare.degreeTree62_84All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.degreeTree62_94All`, `OAI.UniversalTensorSquare.sg32075`, `OAI.UniversalTensorSquare.sg32079`, `OAI.UniversalTensorSquare.sg32082`, `OAI.UniversalTensorSquare.sg32175`, `OAI.UniversalTensorSquare.sg32177`, `OAI.UniversalTensorSquare.sg32183`, `OAI.UniversalTensorSquare.sg32191`, `OAI.UniversalTensorSquare.sg32193`, `OAI.UniversalTensorSquare.sg32197`, `OAI.UniversalTensorSquare.sg32227`, `OAI.UniversalTensorSquare.sg32229`, `OAI.UniversalTensorSquare.sg32237`, `OAI.UniversalTensorSquare.sg32239`, `OAI.UniversalTensorSquare.sg32243`, `OAI.UniversalTensorSquare.sg32249`, `OAI.UniversalTensorSquare.sg32255`, `OAI.UniversalTensorSquare.sg32297`, `OAI.UniversalTensorSquare.sg32299`, `OAI.UniversalTensorSquare.sg32315`, `OAI.UniversalTensorSquare.sg32319`, `OAI.UniversalTensorSquare.sg32321`, `OAI.UniversalTensorSquare.sg32358`, `OAI.UniversalTensorSquare.sg32406`, `OAI.UniversalTensorSquare.sg32426`, `OAI.UniversalTensorSquare.sg32428`, `OAI.UniversalTensorSquare.sg32430`, `OAI.UniversalTensorSquare.sg32432`, `OAI.UniversalTensorSquare.sg32451`, `OAI.UniversalTensorSquare.sg32453`, `OAI.UniversalTensorSquare.sg32459`, `OAI.UniversalTensorSquare.sg32461`, `OAI.UniversalTensorSquare.sg32463`, `OAI.UniversalTensorSquare.sg32465`, `OAI.UniversalTensorSquare.sg32471`, `OAI.UniversalTensorSquare.sg32472`, `OAI.UniversalTensorSquare.sg32659`, `OAI.UniversalTensorSquare.sg32666`, `OAI.UniversalTensorSquare.sg32668`, `OAI.UniversalTensorSquare.sg32684`, `OAI.UniversalTensorSquare.sg32689`, `OAI.UniversalTensorSquare.sg32691`, `OAI.UniversalTensorSquare.sg32695`, `OAI.UniversalTensorSquare.sg32696`, `OAI.UniversalTensorSquare.sg32697`, `OAI.UniversalTensorSquare.sg32699`, `OAI.UniversalTensorSquare.sg32700`, `OAI.UniversalTensorSquare.sg32705`, `OAI.UniversalTensorSquare.sg32706`, `OAI.UniversalTensorSquare.sg32707`, `OAI.UniversalTensorSquare.sg32710`, `OAI.UniversalTensorSquare.sg32711`, `OAI.UniversalTensorSquare.sg32712`, `OAI.UniversalTensorSquare.sg32715`, `OAI.UniversalTensorSquare.sg32786`, `OAI.UniversalTensorSquare.sg32787`, `OAI.UniversalTensorSquare.sg32788`, `OAI.UniversalTensorSquare.sg32832`, `OAI.UniversalTensorSquare.sg32833`, `OAI.UniversalTensorSquare.sg32834`, `OAI.UniversalTensorSquare.sg32938`, `OAI.UniversalTensorSquare.sg33077`, `OAI.UniversalTensorSquare.sg33603`, `OAI.UniversalTensorSquare.sg33613`, `OAI.UniversalTensorSquare.sg33644`, `OAI.UniversalTensorSquare.sg33663`, `OAI.UniversalTensorSquare.sg33786`, `OAI.UniversalTensorSquare.sg34003`, `OAI.UniversalTensorSquare.sg34012`, `OAI.UniversalTensorSquare.sg34018` and `OAI.UniversalTensorSquare.sg40770` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4304)

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

lemma sg4304 : RowSquare [7,4,2,1,1,1] [3,3,3,3,3,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
