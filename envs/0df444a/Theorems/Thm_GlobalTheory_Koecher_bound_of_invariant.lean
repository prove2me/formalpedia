-- Prove2me | Theorems.Thm_GlobalTheory_Koecher_bound_of_invariant
-- name    : GlobalTheory.Koecher.bound_of_invariant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:48:56.139087+00:00
-- url     : https://prove2.me/theorems/2c665d76-d876-415c-8403-e5cfe92600ab
-- title:
--   Koecher: bound of invariant
-- statement:
--   The Koecher construction uses the bound of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L355-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NormLeTsumOfCubeFourierCoeffLe.lean#L355-L389

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

theorem GlobalTheory.Koecher.bound_of_invariant {g : ℕ} {F : Matrix (Fin g) (Fin g) ℂ → ℂ}
    {U : Matrix (Fin g) (Fin g) ℤ} (hU : U.det = 1)
    (hinv : ∀ τ ∈ SiegelH (Fin g),
      F (U.map (Int.cast : ℤ → ℂ) * τ * (U.map (Int.cast : ℤ → ℂ))ᵀ) = F τ)
    {s M : ℝ} (hs : 0 < s)
    (hM : ∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm →
      τ.map Complex.im = s • (1 : Matrix (Fin g) (Fin g) ℝ) → ‖F τ‖ ≤ M)
    (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ.IsSymm)
    (him : τ.map Complex.im =
      s • (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ)) : ‖F τ‖ ≤ M := by sorry
