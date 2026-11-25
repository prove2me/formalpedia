-- Prove2me | Theorems.Thm_GlobalTheory_TorsionPairTest_isAdd_unique
-- name    : GlobalTheory.TorsionPairTest.isAdd_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:44.85191+00:00
-- url     : https://prove2.me/theorems/37119d5e-21c0-5849-ac19-76c7dadc4fdf
-- title:
--   Torsion Pair Test: is Add unique
-- statement:
--   The Torsion Pair Test construction uses the is Add unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L35-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem GlobalTheory.TorsionPairTest.isAdd_unique {T : Over (Spec (CommRingCat.of R))} {g g' a a' : GtPt D T} (h : g.IsAdd g' a)
    (h' : g.IsAdd g' a') : a = a' := by sorry
