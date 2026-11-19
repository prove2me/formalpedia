-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg615
-- name    : OAI.UniversalTensorSquare.sg615
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:52:10.427002+00:00
-- url     : https://prove2.me/theorems/aab0f06b-6db2-46db-9287-c6df0ac4dfc2
-- title:
--   OAI.UniversalTensorSquare.sg615: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg615` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg615 : RowSquare [5,2,1,1] [2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_37All`, `OAI.UniversalTensorSquare.degreeTree41_11All`, `OAI.UniversalTensorSquare.degreeTree41_12All`, `OAI.UniversalTensorSquare.degreeTree43_245All`, `OAI.UniversalTensorSquare.degreeTree43_619All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.sg16497`, `OAI.UniversalTensorSquare.sg16677`, `OAI.UniversalTensorSquare.sg16715`, `OAI.UniversalTensorSquare.sg17617`, `OAI.UniversalTensorSquare.sg21490`, `OAI.UniversalTensorSquare.sg22015`, `OAI.UniversalTensorSquare.sg22136`, `OAI.UniversalTensorSquare.sg22139`, `OAI.UniversalTensorSquare.sg22251`, `OAI.UniversalTensorSquare.sg23189`, `OAI.UniversalTensorSquare.sg23207`, `OAI.UniversalTensorSquare.sg25127`, `OAI.UniversalTensorSquare.sg25174`, `OAI.UniversalTensorSquare.sg26329`, `OAI.UniversalTensorSquare.sg26887`, `OAI.UniversalTensorSquare.sg31442`, `OAI.UniversalTensorSquare.sg31501`, `OAI.UniversalTensorSquare.sg31643`, `OAI.UniversalTensorSquare.sg34695`, `OAI.UniversalTensorSquare.sg34775`, `OAI.UniversalTensorSquare.sg34777`, `OAI.UniversalTensorSquare.sg34880`, `OAI.UniversalTensorSquare.sg34892`, `OAI.UniversalTensorSquare.sg34894`, `OAI.UniversalTensorSquare.sg34896`, `OAI.UniversalTensorSquare.sg34898`, `OAI.UniversalTensorSquare.sg34941`, `OAI.UniversalTensorSquare.sg35003`, `OAI.UniversalTensorSquare.sg35004`, `OAI.UniversalTensorSquare.sg35005`, `OAI.UniversalTensorSquare.sg35051`, `OAI.UniversalTensorSquare.sg35052`, `OAI.UniversalTensorSquare.sg35053`, `OAI.UniversalTensorSquare.sg35085`, `OAI.UniversalTensorSquare.sg41240`, `OAI.UniversalTensorSquare.sg41893`, `OAI.UniversalTensorSquare.sg42242`, `OAI.UniversalTensorSquare.sg42385`, `OAI.UniversalTensorSquare.sg42386`, `OAI.UniversalTensorSquare.sg42387`, `OAI.UniversalTensorSquare.sg42404`, `OAI.UniversalTensorSquare.sg42431`, `OAI.UniversalTensorSquare.sg6798`, `OAI.UniversalTensorSquare.sg6821`, `OAI.UniversalTensorSquare.sg8489`, `OAI.UniversalTensorSquare.sg9937`, `OAI.UniversalTensorSquare.sg9945` and `OAI.UniversalTensorSquare.sg9999` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg615)

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

lemma sg615 : RowSquare [5,2,1,1] [2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
