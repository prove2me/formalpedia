-- Prove2me | Theorems.Thm_GlobalTheory_FieldRestrictionTest_isIota_restrict
-- name    : GlobalTheory.FieldRestrictionTest.isIota_restrict
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:41.279475+00:00
-- url     : https://prove2.me/theorems/38ba482c-2249-59c9-bd6a-9ba046326f59
-- title:
--   Field Restriction Test: is Iota restrict
-- statement:
--   The Field Restriction Test construction uses the is Iota restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L109-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L109-L131

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
variable {W : (Spec (CommRingCat.of R)).Opens} {ψW : PsiOn D W} {S : Over W.toScheme}

theorem GlobalTheory.FieldRestrictionTest.isIota_restrict {σ : TF (R := R) F ⟶ overW W S} {y : D.X} {a : GtPt D (overW W S)} {a' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (h : GtPt.IsIotaW ψW y a) : GtPtF.IsIota y a' := by sorry
