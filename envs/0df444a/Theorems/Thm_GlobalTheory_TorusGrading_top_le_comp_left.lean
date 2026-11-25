-- Prove2me | Theorems.Thm_GlobalTheory_TorusGrading_top_le_comp_left
-- name    : GlobalTheory.TorusGrading.top_le_comp_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:55.846459+00:00
-- url     : https://prove2.me/theorems/d2a91329-b1e7-4d2e-b834-012199c10196
-- title:
--   Torus Grading: top le comp left
-- statement:
--   The Torus Grading construction uses the top le comp left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L139-L141

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
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
omit [GrpObj G]

theorem GlobalTheory.TorusGrading.top_le_comp_left {W Z : Over S} (s : W ⟶ Z) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) :
    ⊤ ≤ (s ≫ g).left ⁻¹ᵁ V := by sorry
