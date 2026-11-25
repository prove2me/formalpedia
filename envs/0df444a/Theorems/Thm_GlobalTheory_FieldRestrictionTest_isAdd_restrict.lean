-- Prove2me | Theorems.Thm_GlobalTheory_FieldRestrictionTest_isAdd_restrict
-- name    : GlobalTheory.FieldRestrictionTest.isAdd_restrict
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:39:14.700886+00:00
-- url     : https://prove2.me/theorems/e52e66b7-787a-5cfa-9945-ceac5de7dc5e
-- title:
--   Field Restriction Test: is Add restrict
-- statement:
--   The Field Restriction Test construction uses the is Add restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L85-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L85-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}

theorem GlobalTheory.FieldRestrictionTest.isAdd_restrict {σ : TF (R := R) F ⟶ T} {a b c : GtPt D T} {a' b' c' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (Hb : GtPt.IsPullF F σ.left b b') (Hc : GtPt.IsPullF F σ.left c c')
    (h : a.IsAdd b c) : a'.IsAdd b' c' := by sorry
