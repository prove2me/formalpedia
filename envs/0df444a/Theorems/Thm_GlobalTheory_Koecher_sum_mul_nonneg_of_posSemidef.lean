-- Prove2me | Theorems.Thm_GlobalTheory_Koecher_sum_mul_nonneg_of_posSemidef
-- name    : GlobalTheory.Koecher.sum_mul_nonneg_of_posSemidef
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:06:21.683073+00:00
-- url     : https://prove2.me/theorems/8b1a88c1-5d1d-47d3-b9d7-cd2b32e8ddff
-- title:
--   Koecher: sum mul nonneg of pos Semidef
-- statement:
--   The Koecher construction uses the sum mul nonneg of pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L322-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L322-L325

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

theorem GlobalTheory.Koecher.sum_mul_nonneg_of_posSemidef {g : ℕ} {T P : Matrix (Fin g) (Fin g) ℝ}
    (hT : T.PosSemidef) (hP : P.PosSemidef) : 0 ≤ ∑ q : Fin g × Fin g, T q.1 q.2 * P q.1 q.2 := by sorry
