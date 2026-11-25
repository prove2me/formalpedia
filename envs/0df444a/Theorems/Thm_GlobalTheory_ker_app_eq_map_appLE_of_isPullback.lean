-- Prove2me | Theorems.Thm_GlobalTheory_ker_app_eq_map_appLE_of_isPullback
-- name    : GlobalTheory.ker_app_eq_map_appLE_of_isPullback
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:32:01.325025+00:00
-- url     : https://prove2.me/theorems/1ea3cf9c-e6cd-5ffd-8585-66c4d31b3faf
-- title:
--   Global Theory: ker app eq map app LE of is Pullback
-- statement:
--   The Global Theory construction uses the ker app eq map app LE of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KerAppEqMapAppLEOfIsPullback.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/KerAppEqMapAppLEOfIsPullback.lean#L18-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Theorems.Thm_GlobalTheory_UU_IsWt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory

theorem GlobalTheory.ker_app_eq_map_appLE_of_isPullback {Y Z : Scheme.{0}} {A C : CommRingCat.{0}}
    {β : A ⟶ C} (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom := by sorry
