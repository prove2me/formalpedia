-- Prove2me | Theorems.Thm_GlobalTheory_RatLift_exists_retraction
-- name    : GlobalTheory.RatLift.exists_retraction
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:44.623386+00:00
-- url     : https://prove2.me/theorems/16e6d1a0-21c6-4fba-bb2a-e79209a2983a
-- title:
--   Rat Lift: exists retraction
-- statement:
--   The Rat Lift construction uses the exists retraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsLiftOfRetraction.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsLiftOfRetraction.lean#L22-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsLiftOfRetraction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RatLift

theorem GlobalTheory.RatLift.exists_retraction {A C X : Type} [CommRing A] [CommRing C] [AddCommGroup X] (f : A →+* C)
    (g : Multiplicative X →* C)
    (h : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _))) :
    ∃ r : C →+* A, r.comp f = RingHom.id A := by sorry
