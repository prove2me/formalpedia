-- Prove2me | Theorems.Thm_GlobalTheory_TorsionPairTest_isIota_unique
-- name    : GlobalTheory.TorsionPairTest.isIota_unique
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:39.160152+00:00
-- url     : https://prove2.me/theorems/be94ce96-bc29-5660-93eb-85dfbfdfba5d
-- title:
--   Torsion Pair Test: is Iota unique
-- statement:
--   The Torsion Pair Test construction uses the is Iota unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L46-L49

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

theorem GlobalTheory.TorsionPairTest.isIota_unique {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) {T : Over W.toScheme} {y : D.X}
    {a a' : GtPt D (overW W T)} (H : GtPt.IsIotaW ψW y a) (H' : GtPt.IsIotaW ψW y a') : a = a' := by sorry
