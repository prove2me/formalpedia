-- Prove2me | Theorems.Thm_GlobalTheory_UU_SchurComp_proportional_field
-- name    : GlobalTheory.UU.SchurComp.proportional_field
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:49.415328+00:00
-- url     : https://prove2.me/theorems/ba6cdde5-dd68-4267-9cb1-6bd84bdfd417
-- title:
--   Schur Comp: proportional field
-- statement:
--   The Schur Comp construction uses the proportional field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L143-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L143-L240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp

theorem GlobalTheory.UU.SchurComp.proportional_field {F : Type} [Field F] {A : Type} [CommGroup A] [Finite A] {E : Type} [AddCommGroup E]
    [Module F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Finite K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Nat.card K * Nat.card H) {n : ℕ} (hn : Nat.card K * n ≤ Module.finrank F E)
    {X Q : Type} [AddCommGroup Q] [Module F Q] (cl : X → K) (ex : X → E →ₗ[F] Q)
    (hinj : ∀ v, (∀ β, ex β v = 0) → v = 0)
    (hP : ∀ k v, ∃ v', ∀ β, (cl β = k → ex β v' = ex β v) ∧ (cl β ≠ k → ex β v' = 0))
    (hne : ∀ k, ∃ β, cl β = k ∧ ∃ v, ex β v ≠ 0)
    (h3 : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v, (∀ γ, cl γ ≠ cl β → ex γ v = 0) → ex β v = 0 → v = 0)
    (hb : ∀ β, ∃ b : Fin n → Q, ∀ v, ex β v ∈ Submodule.span F (Set.range b))
    (hΦ : ∀ h β v, ex β v = 0 → ex β (Φ (m h) v) = 0)
    (α : X) (hα : ∃ v, ex α v ≠ 0) (f₁ f₂ : E →ₗ[F] Q) (hk : ∀ v, f₁ v = 0 ↔ ex α v = 0)
    (b : Fin n → Q) (hb₁ : ∀ v, f₁ v ∈ Submodule.span F (Set.range b))
    (hb₂ : ∀ v, f₂ v ∈ Submodule.span F (Set.range b))
    (hint : ∀ h v v', f₂ v = f₁ v' → f₂ (Φ (m h) v) = f₁ (Φ (m h) v')) : ∃ a : F, ∀ v, f₂ v = a • f₁ v := by sorry
