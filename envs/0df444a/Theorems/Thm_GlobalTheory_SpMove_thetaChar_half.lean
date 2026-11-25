-- Prove2me | Theorems.Thm_GlobalTheory_SpMove_thetaChar_half
-- name    : GlobalTheory.SpMove.thetaChar_half
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:59:42.916724+00:00
-- url     : https://prove2.me/theorems/7d60e5af-6c5f-53be-a777-4d8c62230e00
-- title:
--   Sp Move: theta Char half
-- statement:
--   The Sp Move construction uses the theta Char half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaLawSymplecticNormalForm.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ThetaLawSymplecticNormalForm.lean#L20-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolUnifReparam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EntireEqZeroOrEqZeroOfMulEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaLawSymplecticNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SpMove
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.SpMove.thetaChar_half {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ) (z : Fin g → ℂ) :
    thetaChar τ (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) z = theta (halfVec n) (halfVec n') z τ := by sorry
