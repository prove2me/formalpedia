-- Prove2me | Theorems.Thm_GlobalTheory_TorsionTheta_ptMap_comp_ptMap
-- name    : GlobalTheory.TorsionTheta.ptMap_comp_ptMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:06:57.340515+00:00
-- url     : https://prove2.me/theorems/c7c1fbf5-6d8e-4d6a-bbee-c51fcdd61f79
-- title:
--   Torsion Theta: pt Map comp pt Map
-- statement:
--   The Torsion Theta construction uses the pt Map comp pt Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTorsionPointFrobeniusLocal.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTorsionPointFrobeniusLocal.lean#L14-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTorsionPointFrobeniusLocal
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionTheta

theorem GlobalTheory.TorsionTheta.ptMap_comp_ptMap {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) :
    ptMap ψ ≫ ptMap φ = ptMap (ψ.comp φ) := by sorry
