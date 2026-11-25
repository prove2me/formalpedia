-- Prove2me | Theorems.Thm_GlobalTheory_CoordToExt_prod_square
-- name    : GlobalTheory.CoordToExt.prod_square
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:32.623631+00:00
-- url     : https://prove2.me/theorems/56d7f588-c493-4fda-a559-f57f8f1d2b86
-- title:
--   Coord To Ext: prod square
-- statement:
--   The Coord To Ext construction uses the prod square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L202-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L202-L218

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

theorem GlobalTheory.CoordToExt.prod_square {S : Scheme.{0}} {B T : Over S} [GrpObj B] (x : Fin 2 → (T ⟶ B)) {U : Type} [CommGroup U]
    (F : (T ⟶ B) → U) :
    ∏ J : ULift.{0} (Finset (Fin 2)), F (psum B x J.down) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      F 1 * (F (x 0))⁻¹ * (F (x 1))⁻¹ * F (x 0 * x 1) := by sorry
