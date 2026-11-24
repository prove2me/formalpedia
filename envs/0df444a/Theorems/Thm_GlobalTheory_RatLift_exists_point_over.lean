-- Prove2me | Theorems.Thm_GlobalTheory_RatLift_exists_point_over
-- name    : GlobalTheory.RatLift.exists_point_over
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:50.46327+00:00
-- url     : https://prove2.me/theorems/55707562-a7ed-4197-9ffd-69ed7ef549d4
-- title:
--   Rat Lift: exists point over
-- statement:
--   The Rat Lift construction uses the exists point over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsLiftOfRetraction.lean#L37-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsLiftOfRetraction.lean#L37-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsLiftOfRetraction
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
attribute [local instance] SplitExt.free SplitExt.finite

theorem GlobalTheory.RatLift.exists_point_over :
    ∀ (F : Type) [Field F] (E : SplitExt (Spec (CommRingCat.of F))) (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (Dat : E.GtDatum G) (b : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ E.B), ∃ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G, x ≫ Dat.q = b := by sorry
