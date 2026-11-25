-- Prove2me | Theorems.Thm_GlobalTheory_TorsionPairTest_not_equiv_over_empty
-- name    : GlobalTheory.TorsionPairTest.not_equiv_over_empty
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:37:21.957991+00:00
-- url     : https://prove2.me/theorems/75fd384f-a0b0-5cc3-83c7-a2dd1c219ed9
-- title:
--   Torsion Pair Test: not equiv over empty
-- statement:
--   The Torsion Pair Test construction uses the not equiv over empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L110-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L110-L119

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
variable {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) [IsEmpty T.left]

theorem GlobalTheory.TorsionPairTest.not_equiv_over_empty {W : (Spec (CommRingCat.of InhTate.R)).Opens} (ψW : PsiOn InhTate.tatePre W) :
    ∃ (T : Over W.toScheme) (_ : IsEmpty T.left) (p p' : QkPtW InhTate.tatePre W ψW 2 T), ¬ QkPtW.Equiv p p' := by sorry
