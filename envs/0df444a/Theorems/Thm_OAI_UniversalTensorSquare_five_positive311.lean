-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_five_positive311
-- name    : OAI.UniversalTensorSquare.five_positive311
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:49:40.958836+00:00
-- url     : https://prove2.me/theorems/a4bb350a-e4d4-45a0-b439-3081115fca20
-- title:
--   OAI.UniversalTensorSquare.five_positive311: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.five_positive311` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns`):
--
--   ```lean
--   lemma five_positive311 :
--       0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
--         (canonicalTableau fiveWitness fiveWitness_card)
--         (canonicalTableau fiveWitness fiveWitness_card)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.fiveWitness` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.fiveWitness_card` (definitions bundle `OAIQ259US012` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.five_kronecker_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean (declaration OAI.UniversalTensorSquare.five_positive311)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

noncomputable section

lemma five_positive311 :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) := by
  sorry

universe u

end
end UniversalTensorSquare
end

end OAI
end
