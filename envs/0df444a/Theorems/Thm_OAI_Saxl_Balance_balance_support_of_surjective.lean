-- Prove2me | Theorems.Thm_OAI_Saxl_Balance_balance_support_of_surjective
-- name    : OAI.Saxl.Balance.balance_support_of_surjective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:10:17.270203+00:00
-- url     : https://prove2.me/theorems/12808027-9e39-4ac1-9d74-6332b8347cfd
-- title:
--   OAI.Saxl.Balance.balance_support_of_surjective: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Balance.balance_support_of_surjective` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceInduction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceInduction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Balance`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem balance_support_of_surjective {n d : ℕ} {G X Y : Type*}
--       [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
--       [AddCommGroup Y] [Module ℂ Y]
--       (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
--       (W : Subrepresentation (wordRep n d))
--       (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
--       (z : Fin d → ℤ) (σ : ℕ → ℤ)
--       (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
--       (φ : G →* fiberGroup c) (hφ : Function.Surjective φ)
--       (τ : Representation ℂ G Y)
--       (L : Y →ₗ[ℂ] WordSpace n d)
--       (hm : ∀ y, L y ∈ W) (hs : ∀ y, FixedComponentSums c z σ (L y))
--       (T : Representation.IntertwiningMap τ
--         ((wordRep n d).comp ((fiberGroup c).subtype.comp φ)))
--       (hT : Function.Injective T)
--       (he : ∀ y, coordinateProjection (componentWords c A label) (L y) = T y)
--       (f : Representation.IntertwiningMap
--         (ρ.comp ((fiberGroup c).subtype.comp φ)) τ) (hf : f ≠ 0) :
--       ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.coordinateProjection`, `OAI.Saxl.fiberGroup`, `OAI.Saxl.Balance.FixedComponentSums` and `OAI.Saxl.Balance.componentWords` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.WordSpace` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.Balance.WordPacking.kronecker_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceInduction.lean (declaration OAI.Saxl.Balance.balance_support_of_surjective)

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
namespace Saxl.Balance

theorem balance_support_of_surjective {n d : ℕ} {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (φ : G →* fiberGroup c) (hφ : Function.Surjective φ)
    (τ : Representation ℂ G Y)
    (L : Y →ₗ[ℂ] WordSpace n d)
    (hm : ∀ y, L y ∈ W) (hs : ∀ y, FixedComponentSums c z σ (L y))
    (T : Representation.IntertwiningMap τ
      ((wordRep n d).comp ((fiberGroup c).subtype.comp φ)))
    (hT : Function.Injective T)
    (he : ∀ y, coordinateProjection (componentWords c A label) (L y) = T y)
    (f : Representation.IntertwiningMap
      (ρ.comp ((fiberGroup c).subtype.comp φ)) τ) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  sorry

end Saxl.Balance
end
end

end OAI
end
