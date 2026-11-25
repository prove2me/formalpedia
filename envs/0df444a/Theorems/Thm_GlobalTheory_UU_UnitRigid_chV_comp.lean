-- Prove2me | Theorems.Thm_GlobalTheory_UU_UnitRigid_chV_comp
-- name    : GlobalTheory.UU.UnitRigid.chV_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:41.51325+00:00
-- url     : https://prove2.me/theorems/bf646b44-15ef-4bdc-85ee-a7b4848bd99c
-- title:
--   Unit Rigid: ch V comp
-- statement:
--   The Unit Rigid construction uses the ch V comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L63-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOneOfGroupLike
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitRigid
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem GlobalTheory.UU.UnitRigid.chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by sorry
