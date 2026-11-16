-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_certificate5
-- name    : OAI.UniversalTensorSquare.certificate5
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T22:32:28.615524+00:00
-- url     : https://prove2.me/theorems/f10139c5-6750-4c36-ba8e-d386d8441359
-- title:
--   OAI.UniversalTensorSquare.certificate5: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.certificate5` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns`):
--
--   ```lean
--   lemma certificate5 : contractionInteger [3,1,1] [3,1,1] [5]
--       (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag5 = 20
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.flag5` and `OAI.UniversalTensorSquare.hookPlacement` (definitions bundle `OAIQ259US002` of this split); `OAI.Saxl.Columns.contractionInteger` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.five_positive5` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean (declaration OAI.UniversalTensorSquare.certificate5)

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma certificate5 : contractionInteger [3,1,1] [3,1,1] [5]
    (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag5 = 20 := by
  sorry

end UniversalTensorSquare
end

end OAI
end
