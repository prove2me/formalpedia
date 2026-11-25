-- Prove2me | Theorems.Thm_GlobalTheory_siegel_eq_of_bounded
-- name    : GlobalTheory.siegel_eq_of_bounded
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:03.246333+00:00
-- url     : https://prove2.me/theorems/4ec99e3b-f938-4639-a389-e790bc85e178
-- title:
--   Global Theory: siegel eq of bounded
-- statement:
--   The Global Theory construction uses the siegel eq of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteAbsLeOneMulMemRange.lean#L492-L576
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteAbsLeOneMulMemRange.lean#L492-L576

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}

theorem GlobalTheory.siegel_eq_of_bounded (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (hσ : σ ∈ SiegelH (Fin g)) :
    H τ = H σ := by sorry
