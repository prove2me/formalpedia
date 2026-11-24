-- Prove2me | Theorems.Thm_GlobalTheory_StableGraph_card_stable_eq_card_hom
-- name    : GlobalTheory.StableGraph.card_stable_eq_card_hom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:22:47.724798+00:00
-- url     : https://prove2.me/theorems/fc4c3617-06ec-490a-99fe-77aa4976259b
-- title:
--   Stable Graph: card stable eq card hom
-- statement:
--   The Stable Graph construction uses the card stable eq card hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableEqCardHom.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableEqCardHom.lean#L150-L152

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableEqCardHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
open GlobalTheory.StableGraph

theorem GlobalTheory.StableGraph.card_stable_eq_card_hom : ∀ (O : Type) [CommRing O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] (g₁ : A₁) (g₂ : A₂) (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), (∀ y ∈ M₂, g₂ * y ∈ M₂) → Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} = Nat.card {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁, φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} := by sorry
