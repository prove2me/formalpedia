-- Prove2me | Theorems.Thm_GlobalTheory_TorusGrading_appLE_comp_top
-- name    : GlobalTheory.TorusGrading.appLE_comp_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:31.563926+00:00
-- url     : https://prove2.me/theorems/c1bb6d9e-c037-501d-998b-20b9230abf2e
-- title:
--   Torus Grading: app LE comp top
-- statement:
--   The Torus Grading construction uses the app LE comp top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L27-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
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
open GlobalTheory
open GlobalTheory.TorusGrading

theorem GlobalTheory.TorusGrading.appLE_comp_top {Y Z W : Scheme.{0}} {V : Y.Opens} (s : W ⟶ Z) (g : Z ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ V)
    {g' : W ⟶ Y} (e : s ≫ g = g') (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(Y, V)) :
    (g'.appLE V ⊤ h').hom u = s.appTop.hom ((g.appLE V ⊤ h).hom u) := by sorry
