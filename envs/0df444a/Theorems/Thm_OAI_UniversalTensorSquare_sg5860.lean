-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg5860
-- name    : OAI.UniversalTensorSquare.sg5860
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:23:18.581259+00:00
-- url     : https://prove2.me/theorems/10f246bd-c32e-4df1-bc3b-8154a20ec2f4
-- title:
--   OAI.UniversalTensorSquare.sg5860: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg5860` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes13.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes13.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg5860 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_420All`, `OAI.UniversalTensorSquare.sg29044`, `OAI.UniversalTensorSquare.sg29692`, `OAI.UniversalTensorSquare.sg29693`, `OAI.UniversalTensorSquare.sg29890`, `OAI.UniversalTensorSquare.sg31433`, `OAI.UniversalTensorSquare.sg31487`, `OAI.UniversalTensorSquare.sg31488` and `OAI.UniversalTensorSquare.sg31513` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes13.lean (declaration OAI.UniversalTensorSquare.sg5860)

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

lemma sg5860 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
