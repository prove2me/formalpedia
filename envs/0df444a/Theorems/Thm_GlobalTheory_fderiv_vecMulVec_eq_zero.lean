-- Prove2me | Theorems.Thm_GlobalTheory_fderiv_vecMulVec_eq_zero
-- name    : GlobalTheory.fderiv_vecMulVec_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:19.026851+00:00
-- url     : https://prove2.me/theorems/139a63b9-8e04-43ce-8eef-ff8912040bbe
-- title:
--   Global Theory: fderiv vec Mul Vec eq zero
-- statement:
--   The Global Theory construction uses the fderiv vec Mul Vec eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteAbsLeOneMulMemRange.lean#L458-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteAbsLeOneMulMemRange.lean#L458-L490

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

theorem GlobalTheory.fderiv_vecMulVec_eq_zero (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (e : Fin g) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) :
    fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ)
      (of.symm (vecMulVec (imC τ *ᵥ fun l => (U.val e l : ℂ))
        (imC τ *ᵥ fun l => (U.val e l : ℂ)))) = 0 := by sorry
