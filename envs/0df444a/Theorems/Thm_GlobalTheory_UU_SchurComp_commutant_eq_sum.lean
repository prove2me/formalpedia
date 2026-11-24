-- Prove2me | Theorems.Thm_GlobalTheory_UU_SchurComp_commutant_eq_sum
-- name    : GlobalTheory.UU.SchurComp.commutant_eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:24:21.232819+00:00
-- url     : https://prove2.me/theorems/7669a54a-70f1-4bd0-811a-8588a94031da
-- title:
--   Schur Comp: commutant eq sum
-- statement:
--   The Schur Comp construction uses the commutant eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L6-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L6-L123

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

theorem GlobalTheory.UU.SchurComp.commutant_eq_sum {F : Type} [Field F] {A : Type} [CommGroup A] [Finite A] {E : Type} [AddCommGroup E]
    [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Fintype K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Fintype.card K * Nat.card H) (P : K → E →ₗ[F] E) (hP0 : ∀ k, P k ≠ 0)
    (hP1 : ∀ k v, P k (P k v) = P k v) (hP2 : ∀ k l v, k ≠ l → P k (P l v) = 0)
    (hPΦ : ∀ k h v, P k (Φ (m h) v) = Φ (m h) (P k v)) (φ : E →ₗ[F] E)
    (hφ : ∀ h v, φ (Φ (m h) v) = Φ (m h) (φ v)) : ∃ c : K → F, ∑ k, c k • P k = φ := by sorry
