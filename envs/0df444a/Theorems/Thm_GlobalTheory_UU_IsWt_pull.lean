-- Prove2me | Theorems.Thm_GlobalTheory_UU_IsWt_pull
-- name    : GlobalTheory.UU.IsWt.pull
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:08:18.662607+00:00
-- url     : https://prove2.me/theorems/a2066e03-6893-4392-9903-077df74046dd
-- title:
--   Is Wt: pull
-- statement:
--   The Is Wt construction uses the pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ESecCompOfIsGrpPullback.lean#L93-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ESecCompOfIsGrpPullback.lean#L93-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ESecCompOfIsGrpPullback
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
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem GlobalTheory.UU.IsWt.pull {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (hi : TorusCompat f F i' i) {V : G.left.Opens} {V' : G'.left.Opens} (hV : V' ≤ F ⁻¹ᵁ V) {u : Γ(G.left, V)}
    {χ : X} (hu : IsWt i V u χ) : IsWt i' V' ((F.appLE V V' hV).hom u) χ := by sorry
