-- Prove2me | Theorems.Thm_GlobalTheory_Koecher_posSemidef_of_rat_nonneg
-- name    : GlobalTheory.Koecher.posSemidef_of_rat_nonneg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:53:25.317078+00:00
-- url     : https://prove2.me/theorems/4a8bb899-60ff-4c1e-b41a-030c2c47ff04
-- title:
--   Koecher: pos Semidef of rat nonneg
-- statement:
--   The Koecher construction uses the pos Semidef of rat nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L308-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L308-L320

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.Koecher
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key

theorem GlobalTheory.Koecher.posSemidef_of_rat_nonneg {g : ℕ} {T : Matrix (Fin g) (Fin g) ℤ} (hT : T.IsSymm)
    (h : ∀ v : Fin g → ℚ, 0 ≤ v ⬝ᵥ (T.map (Int.cast : ℤ → ℚ)).mulVec v) :
    (T.map (Int.cast : ℤ → ℝ)).PosSemidef := by sorry
