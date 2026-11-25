-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_lift_of_specialFibre
-- name    : GlobalTheory.exists_valuationSubring_lift_of_specialFibre
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:56.073301+00:00
-- url     : https://prove2.me/theorems/049772a4-5c8b-43cf-92ed-9b79ba53312f
-- title:
--   Global Theory: exists valuation Subring lift of special Fibre
-- statement:
--   The Global Theory construction uses the exists valuation Subring lift of special Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L408-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L408-L431

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem GlobalTheory.exists_valuationSubring_lift_of_specialFibre {Z : Scheme.{u}} (f : Z ⟶ Spec (.of O))
    [Flat f] [LocallyOfFiniteType f]
    {U : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K))))}
    (hU : IsOpen U) (hd : Dense U)
    {z : ↥(pullback f (Spec.map (CommRingCat.ofHom (residue O))))}
    (hz : IsClosed ({z} : Set _)) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z)
      (y' : Spec (.of K') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K)))),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧
      y (closedPoint O') = pullback.fst f (Spec.map (CommRingCat.ofHom (residue O))) z ∧
      y' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y ∧
      y' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
      ∀ t, y' t ∈ U := by sorry
