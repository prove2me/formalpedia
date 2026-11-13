-- Prove2me | Theorems.Thm_OAI_Saxl_pieri_strip_surjective_uts
-- name    : OAI.Saxl.pieri_strip_surjective_uts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:11:31.261677+00:00
-- url     : https://prove2.me/theorems/6d7197e2-37b1-4270-b416-34c537ce1ed4
-- title:
--   OAI.Saxl.pieri_strip_surjective_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.pieri_strip_surjective` of [lean/OAI/RepresentationTheory/Saxl/StripExtension.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/StripExtension.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma pieri_strip_surjective_uts {a n : ℕ} {ν μ : YoungDiagram}
--       (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
--       ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
--         ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
--           (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
--           ∀ x, F (spechtRep t g x) = spechtRep s h (F x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.tableauInclusion` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.HorizontalStrip` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace` and `OAI.Saxl.spechtRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.young_invariant_functional_uts` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/StripExtension.lean (declaration OAI.Saxl.pieri_strip_surjective)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma pieri_strip_surjective_uts {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  sorry

end Saxl

end

end OAI
end
