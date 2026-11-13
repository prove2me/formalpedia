-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg5736
-- name    : OAI.UniversalTensorSquare.sg5736
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:22:37.161962+00:00
-- url     : https://prove2.me/theorems/e3d3ceac-4d34-4d2b-8d75-b6b0740e22bb
-- title:
--   OAI.UniversalTensorSquare.sg5736: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg5736` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes13.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes13.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg5736 : RowSquare [8,3,2,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_181All`, `OAI.UniversalTensorSquare.degreeTree43_185All`, `OAI.UniversalTensorSquare.degreeTree43_191All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_330All`, `OAI.UniversalTensorSquare.degreeTree43_347All`, `OAI.UniversalTensorSquare.degreeTree43_390All`, `OAI.UniversalTensorSquare.degreeTree43_423All`, `OAI.UniversalTensorSquare.degreeTree43_445All`, `OAI.UniversalTensorSquare.degreeTree43_461All`, `OAI.UniversalTensorSquare.degreeTree43_508All`, `OAI.UniversalTensorSquare.degreeTree43_520All`, `OAI.UniversalTensorSquare.degreeTree43_530All`, `OAI.UniversalTensorSquare.degreeTree43_533All`, `OAI.UniversalTensorSquare.degreeTree43_538All`, `OAI.UniversalTensorSquare.sg25813`, `OAI.UniversalTensorSquare.sg28109`, `OAI.UniversalTensorSquare.sg28598`, `OAI.UniversalTensorSquare.sg28713`, `OAI.UniversalTensorSquare.sg28773`, `OAI.UniversalTensorSquare.sg28919`, `OAI.UniversalTensorSquare.sg28980`, `OAI.UniversalTensorSquare.sg29270`, `OAI.UniversalTensorSquare.sg29296`, `OAI.UniversalTensorSquare.sg29391`, `OAI.UniversalTensorSquare.sg29397`, `OAI.UniversalTensorSquare.sg29414`, `OAI.UniversalTensorSquare.sg29452`, `OAI.UniversalTensorSquare.sg29556`, `OAI.UniversalTensorSquare.sg29895`, `OAI.UniversalTensorSquare.sg30076`, `OAI.UniversalTensorSquare.sg30182`, `OAI.UniversalTensorSquare.sg30233`, `OAI.UniversalTensorSquare.sg30336`, `OAI.UniversalTensorSquare.sg30382`, `OAI.UniversalTensorSquare.sg30479` and `OAI.UniversalTensorSquare.sg31778` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes13.lean (declaration OAI.UniversalTensorSquare.sg5736)

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

lemma sg5736 : RowSquare [8,3,2,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
