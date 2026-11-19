-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_of_shapes
-- name    : OAI.UniversalTensorSquare.kronecker_pos_of_shapes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:10:07.49206+00:00
-- url     : https://prove2.me/theorems/82e27de2-6cad-4c14-a06c-ef6d1a77b8e7
-- title:
--   OAI.UniversalTensorSquare.kronecker_pos_of_shapes: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.kronecker_pos_of_shapes` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/SquareSemigroup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SquareSemigroup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`, `open Saxl`):
--
--   ```lean
--   lemma kronecker_pos_of_shapes {n : ℕ} {α β μ A B T : YoungDiagram}
--       (ha : α = A) (hb : β = B) (ht : μ = T)
--       (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
--       (c : Tableau n A) (d : Tableau n B) (u : Tableau n T)
--       (h : 0 < kronecker a b t) : 0 < kronecker c d u
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Tableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.SquareOccurs.pos` and `OAI.UniversalTensorSquare.treeResidual_sound` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SquareSemigroup.lean (declaration OAI.UniversalTensorSquare.kronecker_pos_of_shapes)

import Mathlib
import Definitions.Def_UniversalTensorSquares

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
open Saxl

lemma kronecker_pos_of_shapes {n : ℕ} {α β μ A B T : YoungDiagram}
    (ha : α = A) (hb : β = B) (ht : μ = T)
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (c : Tableau n A) (d : Tableau n B) (u : Tableau n T)
    (h : 0 < kronecker a b t) : 0 < kronecker c d u := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
