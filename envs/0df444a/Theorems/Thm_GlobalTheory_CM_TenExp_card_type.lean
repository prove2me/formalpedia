-- Prove2me | Theorems.Thm_GlobalTheory_CM_TenExp_card_type
-- name    : GlobalTheory.CM.TenExp.card_type
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:55.46294+00:00
-- url     : https://prove2.me/theorems/77e964ef-7949-412c-af68-221cacf532b7
-- title:
--   Ten Exp: card type
-- statement:
--   The Ten Exp construction uses the card type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L118-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsDiagonalCoordinates.lean#L118-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.TenExp
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CM.TenExp.card_type {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : M →+ (Fin g → ℂ)} (hP : ∀ (s : 𝓞 E) a i, P (s • a) i = ty i (s : E) * P a i)
    (hs : Submodule.span ℂ (Set.range P) = ⊤) {w : 𝓞 E} {ω : ℂ} (hw : ∀ a, P (w • a) = ω • P a)
    (hu : ∀ f : M →+ ℂ, (∀ a, f (w • a) = ω • f a) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ a, F (P a) = f a)
    (τ : E →+* ℂ) : (τ w = ω → Nat.card {i // ty i = τ} = Module.finrank (𝓞 E) M) ∧
      (τ w ≠ ω → Nat.card {i // ty i = τ} = 0) := by sorry
