-- Prove2me | Theorems.Thm_GlobalTheory_FieldRestrictionTest_existsUnique_pair_iff
-- name    : GlobalTheory.FieldRestrictionTest.existsUnique_pair_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:19.36934+00:00
-- url     : https://prove2.me/theorems/5d0514f8-bb25-4f96-9d9f-7b2245077ae4
-- title:
--   Field Restriction Test: exists Unique pair iff
-- statement:
--   The Field Restriction Test construction uses the exists Unique pair iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L133-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L133-L143

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

theorem GlobalTheory.FieldRestrictionTest.existsUnique_pair_iff {k : ℕ} (x : Spec (CommRingCat.of F) ⟶ S.left) (p : QkPtW D W ψW k S) :
    (∃! q : QkPt D F k, QkPtW.IsPullF F x p q) ↔ x ≫ S.hom ≫ W.ι = jFK (R := R) F ≫ jK R := by sorry
