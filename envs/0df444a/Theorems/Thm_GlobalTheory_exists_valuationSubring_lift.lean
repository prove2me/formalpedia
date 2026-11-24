-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_lift
-- name    : GlobalTheory.exists_valuationSubring_lift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:45:25.884224+00:00
-- url     : https://prove2.me/theorems/aa0d1d42-bb4c-496f-9e7f-7f8c0e62fbd1
-- title:
--   Global Theory: exists valuation Subring lift
-- statement:
--   The Global Theory construction uses the exists valuation Subring lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L371-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L371-L406

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

theorem GlobalTheory.exists_valuationSubring_lift {Z : Scheme.{u}} (f : Z ⟶ Spec (.of O))
    [Flat f] [LocallyOfFiniteType f]
    {U : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K))))}
    (hU : IsOpen U) (hd : Dense U)
    {z : Z} (hz : IsClosed ({z} : Set Z)) (hzO : f z = closedPoint O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z)
      (y' : Spec (.of K') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K)))),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧ y (closedPoint O') = z ∧
      y' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y ∧
      y' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
      ∀ t, y' t ∈ U := by sorry
