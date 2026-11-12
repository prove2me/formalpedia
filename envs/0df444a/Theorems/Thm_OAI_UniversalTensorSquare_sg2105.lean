-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2105
-- name    : OAI.UniversalTensorSquare.sg2105
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:57:51.532199+00:00
-- url     : https://prove2.me/theorems/b2ccc242-d1b3-4ff2-958a-321ee853249e
-- title:
--   OAI.UniversalTensorSquare.sg2105: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2105` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2105 : RowSquare [4,4,1,1,1,1,1] [13]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_307All`, `OAI.UniversalTensorSquare.degreeTree43_311All`, `OAI.UniversalTensorSquare.degreeTree43_315All`, `OAI.UniversalTensorSquare.degreeTree43_316All`, `OAI.UniversalTensorSquare.degreeTree43_327All`, `OAI.UniversalTensorSquare.degreeTree43_333All`, `OAI.UniversalTensorSquare.degreeTree43_336All`, `OAI.UniversalTensorSquare.degreeTree43_343All`, `OAI.UniversalTensorSquare.degreeTree43_371All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.sg11814`, `OAI.UniversalTensorSquare.sg21132`, `OAI.UniversalTensorSquare.sg21139`, `OAI.UniversalTensorSquare.sg26984`, `OAI.UniversalTensorSquare.sg27633`, `OAI.UniversalTensorSquare.sg27641`, `OAI.UniversalTensorSquare.sg27812`, `OAI.UniversalTensorSquare.sg27854`, `OAI.UniversalTensorSquare.sg27855`, `OAI.UniversalTensorSquare.sg28003`, `OAI.UniversalTensorSquare.sg28049`, `OAI.UniversalTensorSquare.sg28164`, `OAI.UniversalTensorSquare.sg28447`, `OAI.UniversalTensorSquare.sg28502`, `OAI.UniversalTensorSquare.sg29142`, `OAI.UniversalTensorSquare.sg29162`, `OAI.UniversalTensorSquare.sg29172`, `OAI.UniversalTensorSquare.sg29956`, `OAI.UniversalTensorSquare.sg29957` and `OAI.UniversalTensorSquare.sg29966` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg2105)

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

lemma sg2105 : RowSquare [4,4,1,1,1,1,1] [13] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
