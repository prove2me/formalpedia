-- Prove2me | Theorems.Thm_GlobalTheory_UU_UnitRigid_eq_one_of_groupLike
-- name    : GlobalTheory.UU.UnitRigid.eq_one_of_groupLike
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:46.612283+00:00
-- url     : https://prove2.me/theorems/7c317d12-8d52-5f4d-ba5e-a3a74372ed9a
-- title:
--   Unit Rigid: eq one of group Like
-- statement:
--   The Unit Rigid construction uses the eq one of group Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L39-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L39-L59

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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

theorem GlobalTheory.UU.UnitRigid.eq_one_of_groupLike {B X : Type} [CommRing B] [AddCommGroup X] (I : Ideal B) (hI : ∀ b ∈ I, IsNilpotent b)
    (g : AddMonoidAlgebra B X)
    (h : AddMonoidAlgebra.mapDomainRingHom B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) g =
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) g *
        AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) g)
    (h₁ : AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I) g = 1) : g = 1 := by sorry
