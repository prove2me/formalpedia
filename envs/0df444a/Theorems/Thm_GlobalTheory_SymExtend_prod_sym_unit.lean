-- Prove2me | Theorems.Thm_GlobalTheory_SymExtend_prod_sym_unit
-- name    : GlobalTheory.SymExtend.prod_sym_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:13:18.017175+00:00
-- url     : https://prove2.me/theorems/653ba9e4-d9e8-488c-95de-42b302db85cf
-- title:
--   Sym Extend: prod sym unit
-- statement:
--   The Sym Extend construction uses the prod sym unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCpOfGenericPolarisation.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCpOfGenericPolarisation.lean#L47-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalExtendsAndExtendGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedIsoRespectsCubeAndSymmetry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCpOfGenericPolarisation
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

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
open GlobalTheory GlobalTheory.SymExtend

theorem GlobalTheory.SymExtend.prod_sym_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (U : Type) [CommGroup U]
    (h : (S ⟶ G.left) → U) :
    ∏ k : Fin 2, h (eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by sorry
