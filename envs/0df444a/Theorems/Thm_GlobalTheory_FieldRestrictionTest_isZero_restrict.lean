-- Prove2me | Theorems.Thm_GlobalTheory_FieldRestrictionTest_isZero_restrict
-- name    : GlobalTheory.FieldRestrictionTest.isZero_restrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:49:52.19309+00:00
-- url     : https://prove2.me/theorems/2c23eddf-d021-5b88-8614-0f6f00da200b
-- title:
--   Field Restriction Test: is Zero restrict
-- statement:
--   The Field Restriction Test construction uses the is Zero restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L79-L83

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

theorem GlobalTheory.FieldRestrictionTest.isZero_restrict {σ : TF (R := R) F ⟶ T} {g : GtPt D T} {g' : GtPtF D F} (H : GtPt.IsPullF F σ.left g g')
    (h : g.IsZero) : g'.IsZero := by sorry
