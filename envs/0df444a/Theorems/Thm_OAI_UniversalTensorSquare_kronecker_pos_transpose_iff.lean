-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose_iff
-- name    : OAI.UniversalTensorSquare.kronecker_pos_transpose_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:10:12.964901+00:00
-- url     : https://prove2.me/theorems/fec7fe7b-7d7b-4171-893c-5cb9dd2aa43c
-- title:
--   OAI.UniversalTensorSquare.kronecker_pos_transpose_iff: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.kronecker_pos_transpose_iff` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/TransposeSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/TransposeSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem kronecker_pos_transpose_iff {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
--       (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n) :
--       (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
--         (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ↔
--       (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
--         (Saxl.canonicalTableau lam hlam)
--         (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.transpose_card` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.balance_kronecker_pos_or_transpose`, `OAI.UniversalTensorSquare.candidate_refined_pos` and `OAI.UniversalTensorSquare.candidate_semantic_pos` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/TransposeSupport.lean (declaration OAI.UniversalTensorSquare.kronecker_pos_transpose_iff)

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

theorem kronecker_pos_transpose_iff {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
