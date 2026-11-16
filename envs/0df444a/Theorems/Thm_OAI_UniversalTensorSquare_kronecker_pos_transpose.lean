-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
-- name    : OAI.UniversalTensorSquare.kronecker_pos_transpose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:48:14.739968+00:00
-- url     : https://prove2.me/theorems/2ca0b4f6-b53b-4cc2-b885-9b17b3c5136a
-- title:
--   OAI.UniversalTensorSquare.kronecker_pos_transpose: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.kronecker_pos_transpose` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/TransposeSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/TransposeSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma kronecker_pos_transpose {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
--       (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n)
--       (hpos : 0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
--         (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
--       0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
--         (Saxl.canonicalTableau lam hlam)
--         (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.transpose_card` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_123All`, `OAI.UniversalTensorSquare.degreeTree39_13All`, `OAI.UniversalTensorSquare.degreeTree39_14All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree41_9All`, `OAI.UniversalTensorSquare.degreeTree43_112All`, `OAI.UniversalTensorSquare.five_kronecker_pos` and `OAI.UniversalTensorSquare.seven_kronecker_pos` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/TransposeSupport.lean (declaration OAI.UniversalTensorSquare.kronecker_pos_transpose)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

lemma kronecker_pos_transpose {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n)
    (hpos : 0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν)) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
