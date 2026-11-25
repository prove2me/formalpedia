-- Prove2me | Theorems.Thm_GlobalTheory_CoordToExt_coordUnit_trans
-- name    : GlobalTheory.CoordToExt.coordUnit_trans
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:43.328455+00:00
-- url     : https://prove2.me/theorems/d8f32966-c6ef-4a13-8bf2-2ce619599548
-- title:
--   Coord To Ext: coord Unit trans
-- statement:
--   The Coord To Ext construction uses the coord Unit trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L311-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L311-L327

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)
variable {I D e} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem GlobalTheory.CoordToExt.coordUnit_trans (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z)
    (a a' : (bundle I D e χ).ι) (h : g.q.left (r z) ∈ (bundle I D e χ).U a)
    (h' : g.q.left (r z) ∈ (bundle I D e χ).U a') :
    gm r z _ (coordUnit g χ a') = gm (r ≫ g.q.left) z _ ((bundle I D e χ).g a a') * gm r z _ (coordUnit g χ a) := by sorry
