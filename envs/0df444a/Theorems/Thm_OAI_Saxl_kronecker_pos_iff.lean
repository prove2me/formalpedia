-- Prove2me | Theorems.Thm_OAI_Saxl_kronecker_pos_iff
-- name    : OAI.Saxl.kronecker_pos_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:17.67672+00:00
-- url     : https://prove2.me/theorems/f6d4d8e7-6002-4e53-a3f0-c4739f7c5fd9
-- title:
--   OAI.Saxl.kronecker_pos_iff: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.kronecker_pos_iff` of [lean/OAI/RepresentationTheory/Saxl/Basic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/Basic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
--       (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
--       0 < kronecker a b t ↔
--         ∃ f : Representation.IntertwiningMap (spechtRep t)
--           ((spechtRep a).tprod (spechtRep b)), f ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.kronecker` and `OAI.Saxl.spechtRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.SquareOccurs.input_transpose`, `OAI.UniversalTensorSquare.balance_kronecker_pos_or_transpose`, `OAI.UniversalTensorSquare.candidate_refined_pos`, `OAI.UniversalTensorSquare.kronecker_pos_of_shapes`, `OAI.UniversalTensorSquare.kronecker_pos_transpose_iff` and `OAI.UniversalTensorSquare.rowSquare_even` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/Basic.lean (declaration OAI.Saxl.kronecker_pos_iff)

import Mathlib
import Definitions.Def_UniversalTensorSquares

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  sorry

end Saxl

end

end OAI
end
