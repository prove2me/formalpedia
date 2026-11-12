-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_universal_tensor_square_le_ten
-- name    : OAI.UniversalTensorSquare.universal_tensor_square_le_ten
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:07:15.645001+00:00
-- url     : https://prove2.me/theorems/3558ac82-61f8-4eec-b887-6e3b1cc5540a
-- title:
--   OAI.UniversalTensorSquare.universal_tensor_square_le_ten: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.universal_tensor_square_le_ten` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/SmallDegrees.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SmallDegrees.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`):
--
--   ```lean
--   theorem universal_tensor_square_le_ten
--       (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9)
--       (hsmall : n ≤ 10) :
--       ∃ (lam : YoungDiagram) (hlam : lam.card = n),
--         (∀ (ν : YoungDiagram) (hν : ν.card = n),
--           0 < kronecker (canonicalTableau lam hlam)
--             (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
--         Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
--         ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
--           (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
--           ∃ F : Representation.IntertwiningMap ρ
--             ((spechtRep (canonicalTableau lam hlam)).tprod
--               (spechtRep (canonicalTableau lam hlam))), Function.Injective F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Specht`, `OAI.Saxl.WordSpace`, `OAI.Saxl.canonicalTableau`, `OAI.Saxl.kronecker` and `OAI.Saxl.spechtRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.universal_partition_le64` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SmallDegrees.lean (declaration OAI.UniversalTensorSquare.universal_tensor_square_le_ten)

import Mathlib
import Definitions.Def_UniversalTensorSquares

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare
open Saxl

universe u

theorem universal_tensor_square_le_ten
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9)
    (hsmall : n ≤ 10) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  sorry

end UniversalTensorSquare
end

end OAI
end
