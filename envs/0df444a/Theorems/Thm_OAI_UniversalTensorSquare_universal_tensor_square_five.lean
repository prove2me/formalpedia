-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_universal_tensor_square_five
-- name    : OAI.UniversalTensorSquare.universal_tensor_square_five
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:06:45.590013+00:00
-- url     : https://prove2.me/theorems/60c12d33-1c8b-4901-aeb0-597ee299df11
-- title:
--   OAI.UniversalTensorSquare.universal_tensor_square_five: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.universal_tensor_square_five` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`):
--
--   ```lean
--   theorem universal_tensor_square_five :
--       ∃ (lam : YoungDiagram) (hlam : lam.card = 5),
--         (∀ (ν : YoungDiagram) (hν : ν.card = 5),
--           0 < kronecker (canonicalTableau lam hlam)
--             (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
--         Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
--         ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
--           (ρ : Representation ℂ (Equiv.Perm (Fin 5)) V) [Representation.IsIrreducible ρ],
--           ∃ F : Representation.IntertwiningMap ρ
--             ((spechtRep (canonicalTableau lam hlam)).tprod
--               (spechtRep (canonicalTableau lam hlam))), Function.Injective F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Specht`, `OAI.Saxl.WordSpace`, `OAI.Saxl.canonicalTableau`, `OAI.Saxl.kronecker` and `OAI.Saxl.spechtRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.universal_tensor_square_le_ten` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean (declaration OAI.UniversalTensorSquare.universal_tensor_square_five)

import Mathlib
import Definitions.Def_UniversalTensorSquares

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Saxl
namespace UniversalTensorSquare

noncomputable section

universe u

theorem universal_tensor_square_five :
    ∃ (lam : YoungDiagram) (hlam : lam.card = 5),
      (∀ (ν : YoungDiagram) (hν : ν.card = 5),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin 5)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  sorry

end
end UniversalTensorSquare
end

end OAI
end
