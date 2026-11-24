-- Prove2me | Theorems.Thm_GlobalTheory_KeyPow_exists_sec_div
-- name    : GlobalTheory.KeyPow.exists_sec_div
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:43:43.234151+00:00
-- url     : https://prove2.me/theorems/c1382497-ab61-4492-9896-c44d270a249b
-- title:
--   Key Pow: exists sec div
-- statement:
--   The Key Pow construction uses the exists sec div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ValueAtNormalForm.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ValueAtNormalForm.lean#L35-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ValueAtNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X}

theorem GlobalTheory.KeyPow.exists_sec_div {a b : R} (h : a * b = 1) (s : L.Sec) :
    ∃ t : L.Sec, (∀ i, t.f i = constFn p _ b * s.f i) ∧ (∀ i, s.f i = constFn p _ a * t.f i) ∧
      Out.nonzeroLocus s ≤ Out.nonzeroLocus t := by sorry
