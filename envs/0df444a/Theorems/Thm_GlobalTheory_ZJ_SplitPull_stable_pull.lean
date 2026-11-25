-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_SplitPull_stable_pull
-- name    : GlobalTheory.ZJ.SplitPull.stable_pull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:41:17.488732+00:00
-- url     : https://prove2.me/theorems/67871459-8715-4308-8412-861460331f01
-- title:
--   Split Pull: stable pull
-- statement:
--   The Split Pull construction uses the stable pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPullAndSplitPull.lean#L109-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G]
  [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G}
  {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i)
include hF hi

theorem GlobalTheory.ZJ.SplitPull.stable_pull {V : G.left.Opens} (hV : Stable i V) : Stable i' (F ⁻¹ᵁ V) := by sorry
