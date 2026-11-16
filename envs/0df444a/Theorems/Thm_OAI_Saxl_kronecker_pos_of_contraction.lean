-- Prove2me | Theorems.Thm_OAI_Saxl_kronecker_pos_of_contraction
-- name    : OAI.Saxl.kronecker_pos_of_contraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:31:29.620313+00:00
-- url     : https://prove2.me/theorems/625cdd02-a9da-4127-82ad-c996ecee7797
-- title:
--   OAI.Saxl.kronecker_pos_of_contraction: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.kronecker_pos_of_contraction` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SquareDetection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SquareDetection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem kronecker_pos_of_contraction {n : ℕ} {α β μ : YoungDiagram}
--       (a a' : Tableau n α) (b b' : Tableau n β) (t s : Tableau n μ)
--       (L : Fin (μ.colLen 0) → Fin (α.colLen 0 * β.colLen 0) → ℂ)
--       (h : dotProduct (wordMap L (polytabloid s))
--         (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0) :
--       0 < kronecker a b t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.wordMap` and `OAI.Saxl.wordTensor` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.kronecker`, `OAI.Saxl.polytabloid` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_123All`, `OAI.UniversalTensorSquare.degreeTree39_13All`, `OAI.UniversalTensorSquare.degreeTree39_14All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree41_9All`, `OAI.UniversalTensorSquare.degreeTree43_112All`, `OAI.UniversalTensorSquare.eight_positive1`, `OAI.UniversalTensorSquare.eight_positive11`, `OAI.UniversalTensorSquare.eight_positive2`, `OAI.UniversalTensorSquare.eight_positive3`, `OAI.UniversalTensorSquare.eight_positive4`, `OAI.UniversalTensorSquare.eight_positive6`, `OAI.UniversalTensorSquare.eight_positive8`, `OAI.UniversalTensorSquare.eight_positive9`, `OAI.UniversalTensorSquare.five_positive_certificate` and `OAI.UniversalTensorSquare.seven_kronecker_pos` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SquareDetection.lean (declaration OAI.Saxl.kronecker_pos_of_contraction)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem kronecker_pos_of_contraction {n : ℕ} {α β μ : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) (t s : Tableau n μ)
    (L : Fin (μ.colLen 0) → Fin (α.colLen 0 * β.colLen 0) → ℂ)
    (h : dotProduct (wordMap L (polytabloid s))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0) :
    0 < kronecker a b t := by
  sorry

end Saxl
end
end

end OAI
end
