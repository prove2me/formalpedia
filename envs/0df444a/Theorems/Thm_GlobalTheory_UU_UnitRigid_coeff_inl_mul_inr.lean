-- Prove2me | Theorems.Thm_GlobalTheory_UU_UnitRigid_coeff_inl_mul_inr
-- name    : GlobalTheory.UU.UnitRigid.coeff_inl_mul_inr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:15.510435+00:00
-- url     : https://prove2.me/theorems/ba5e9859-76b8-55b2-a759-04bb3ba2e2d7
-- title:
--   Unit Rigid: coeff inl mul inr
-- statement:
--   The Unit Rigid construction uses the coeff inl mul inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L23-L37

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

theorem GlobalTheory.UU.UnitRigid.coeff_inl_mul_inr {B X : Type} [CommRing B] [AddCommGroup X] (a b : AddMonoidAlgebra B X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) a *
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) b).coeff (x, y) = a.coeff x * b.coeff y := by sorry
