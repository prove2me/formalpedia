-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4846
-- name    : OAI.UniversalTensorSquare.sg4846
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:35:29.439557+00:00
-- url     : https://prove2.me/theorems/ecfbe319-0918-4444-a982-8489a2fe054a
-- title:
--   OAI.UniversalTensorSquare.sg4846: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4846` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4846 : RowSquare [6,4,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_188All`, `OAI.UniversalTensorSquare.sg20498`, `OAI.UniversalTensorSquare.sg36588`, `OAI.UniversalTensorSquare.sg36612`, `OAI.UniversalTensorSquare.sg36771`, `OAI.UniversalTensorSquare.sg36844`, `OAI.UniversalTensorSquare.sg37003`, `OAI.UniversalTensorSquare.sg37046`, `OAI.UniversalTensorSquare.sg37055`, `OAI.UniversalTensorSquare.sg37907`, `OAI.UniversalTensorSquare.sg37971`, `OAI.UniversalTensorSquare.sg38057`, `OAI.UniversalTensorSquare.sg38195`, `OAI.UniversalTensorSquare.sg38327`, `OAI.UniversalTensorSquare.sg38358`, `OAI.UniversalTensorSquare.sg38364`, `OAI.UniversalTensorSquare.sg38597`, `OAI.UniversalTensorSquare.sg38696`, `OAI.UniversalTensorSquare.sg38754`, `OAI.UniversalTensorSquare.sg38894`, `OAI.UniversalTensorSquare.sg39052`, `OAI.UniversalTensorSquare.sg39119`, `OAI.UniversalTensorSquare.sg39174`, `OAI.UniversalTensorSquare.sg39375`, `OAI.UniversalTensorSquare.sg39466`, `OAI.UniversalTensorSquare.sg39494`, `OAI.UniversalTensorSquare.sg39519`, `OAI.UniversalTensorSquare.sg39708`, `OAI.UniversalTensorSquare.sg39862`, `OAI.UniversalTensorSquare.sg40049`, `OAI.UniversalTensorSquare.sg40174`, `OAI.UniversalTensorSquare.sg40183`, `OAI.UniversalTensorSquare.sg40221`, `OAI.UniversalTensorSquare.sg40502`, `OAI.UniversalTensorSquare.sg40517`, `OAI.UniversalTensorSquare.sg40903`, `OAI.UniversalTensorSquare.sg40942`, `OAI.UniversalTensorSquare.sg40994`, `OAI.UniversalTensorSquare.sg41078`, `OAI.UniversalTensorSquare.sg41159`, `OAI.UniversalTensorSquare.sg41177`, `OAI.UniversalTensorSquare.sg41180`, `OAI.UniversalTensorSquare.sg41577`, `OAI.UniversalTensorSquare.sg41645`, `OAI.UniversalTensorSquare.sg41757`, `OAI.UniversalTensorSquare.sg41811`, `OAI.UniversalTensorSquare.sg41838`, `OAI.UniversalTensorSquare.sg41943`, `OAI.UniversalTensorSquare.sg42026` and `OAI.UniversalTensorSquare.sg42201` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes10.lean (declaration OAI.UniversalTensorSquare.sg4846)

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

lemma sg4846 : RowSquare [6,4,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
