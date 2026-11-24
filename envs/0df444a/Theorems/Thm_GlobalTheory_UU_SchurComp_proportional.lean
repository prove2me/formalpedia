-- Prove2me | Theorems.Thm_GlobalTheory_UU_SchurComp_proportional
-- name    : GlobalTheory.UU.SchurComp.proportional
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:43.762844+00:00
-- url     : https://prove2.me/theorems/cb14f810-66ce-4192-9740-e1ce34b83c8d
-- title:
--   Schur Comp: proportional
-- statement:
--   The Schur Comp construction uses the proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L242-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L242-L280

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

theorem GlobalTheory.UU.SchurComp.proportional {F : Type} [CommRing F] (hF : IsField F) {A : Type} [CommGroup A] [Finite A] {E : Type}
    [AddCommGroup E] [Module F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Finite K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Nat.card K * Nat.card H) {n : ℕ} (hn : Nat.card K * n ≤ Module.finrank F E)
    {X Q : Type} [CommRing Q] (ι : F →+* Q) (cl : X → K) (ex : X → E → Q)
    (hex : ∀ β c v v', ex β (c • v + v') = ι c * ex β v + ex β v')
    (hinj : ∀ v, (∀ β, ex β v = 0) → v = 0)
    (hP : ∀ k v, ∃ v', ∀ β, (cl β = k → ex β v' = ex β v) ∧ (cl β ≠ k → ex β v' = 0))
    (hne : ∀ k, ∃ β, cl β = k ∧ ∃ v, ex β v ≠ 0)
    (h3 : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v, (∀ γ, cl γ ≠ cl β → ex γ v = 0) → ex β v = 0 → v = 0)
    (hb : ∀ β, ∃ b : Fin n → Q, ∀ v, ∃ c : Fin n → F, ex β v = ∑ i, ι (c i) * b i)
    (hΦ : ∀ h β v, ex β v = 0 → ex β (Φ (m h) v) = 0)
    (α α' : X) (hα : ∃ v, ex α v ≠ 0) (f₁ : E → Q) (hf₁ : ∀ c v v', f₁ (c • v + v') = ι c * f₁ v + f₁ v')
    (hk : ∀ v, f₁ v = 0 ↔ ex α v = 0)
    (b : Fin n → Q) (hb₁ : ∀ v, ∃ c : Fin n → F, f₁ v = ∑ i, ι (c i) * b i)
    (hb₂ : ∀ v, ∃ c : Fin n → F, ex α' v = ∑ i, ι (c i) * b i)
    (hint : ∀ h v v', ex α' v = f₁ v' → ex α' (Φ (m h) v) = f₁ (Φ (m h) v')) :
    ∃ a : F, ∀ v, ex α' v = ι a * f₁ v := by sorry
