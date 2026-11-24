-- Prove2me | Theorems.Thm_GlobalTheory_eq_on_rankOneCurve_of_integral
-- name    : GlobalTheory.eq_on_rankOneCurve_of_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:59.318443+00:00
-- url     : https://prove2.me/theorems/2c9b1977-995f-42d4-95ff-0c5a80c254a5
-- title:
--   Global Theory: eq on rank One Curve of integral
-- statement:
--   The Global Theory construction uses the eq on rank One Curve of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteAbsLeOneMulMemRange.lean#L155-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteAbsLeOneMulMemRange.lean#L155-L299

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
variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)
include hZs hZe hZ

theorem GlobalTheory.eq_on_rankOneCurve_of_integral (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {N : ℕ} (hN : N ≠ 0) {R : Matrix (Fin g) (Fin g) ℝ} {u : Fin g → ℝ} (hu : u e = 1)
    (hR : R.IsSymm) (hRe : R e e = 0) (huN : ∀ i, N * u i ∈ (Int.castRingHom ℝ).range)
    (hRN : ∀ i, N * R i e ∈ (Int.castRingHom ℝ).range)
    (hRN2 : ∀ i j, N * N * R i j ∈ (Int.castRingHom ℝ).range) (z w : ℍ) :
    H (rankOneCurve Z R u z) = H (rankOneCurve Z R u w) := by sorry
