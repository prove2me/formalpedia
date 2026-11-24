-- Prove2me | Theorems.Thm_GlobalTheory_IsAffineQuotient_of_isPullback_of_flat_or_sum_eq_one
-- name    : GlobalTheory.IsAffineQuotient.of_isPullback_of_flat_or_sum_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:16.644592+00:00
-- url     : https://prove2.me/theorems/2cb13acb-7722-4459-853e-4e0be7016e93
-- title:
--   Is Affine Quotient: of is Pullback of flat or sum eq one
-- statement:
--   The Is Affine Quotient construction uses the of is Pullback of flat or sum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L700-L756
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L700-L756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y X' Y' S S' : Scheme.{u}}
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
open GlobalTheory.IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π)
  {ρ' : G →* Aut X'} {π' : X' ⟶ Y'} {p : X' ⟶ X} {t : Y' ⟶ Y} (H : IsPullback p π' π t)
  (hp : ∀ g, (ρ' g).hom ≫ p = p ≫ (ρ g).hom) (hπ' : ∀ g, (ρ' g).hom ≫ π' = π')
include h H hp hπ'

theorem GlobalTheory.IsAffineQuotient.of_isPullback_of_flat_or_sum_eq_one [Fintype G]
    (hW : ∀ (W : Y.Opens) (_ : IsAffineOpen W) (W' : Y'.Opens) (_ : IsAffineOpen W')
      (e : W' ≤ t ⁻¹ᵁ W), (t.appLE W W' e).hom.Flat ∨
        letI := sectionsAction ρ _ (h.preimage_le W)
        ∃ c : Γ(X, π ⁻¹ᵁ W), ∑ g : G, g • c = 1) :
    IsAffineQuotient ρ' π' := by sorry
