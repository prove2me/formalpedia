-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_map_eq_pow_mul
-- name    : GlobalTheory.TorsionZero.map_eq_pow_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:47.909668+00:00
-- url     : https://prove2.me/theorems/134d7b86-fb2c-4132-8b4a-a024800b0705
-- title:
--   Torsion Zero: map eq pow mul
-- statement:
--   The Torsion Zero construction uses the map eq pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L226-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L226-L237

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

theorem GlobalTheory.TorsionZero.map_eq_pow_mul {σ : Type} {x : σ → R} {φ ψ : R →ₐ[K] K} {c : K}
    (h : ∀ j, φ (x j) = ψ (x j) * c) {i : σ} (hi : φ (x i) ≠ 0) {y : R} {e n : ℕ}
    {G : MvPolynomial σ K} (hG : G.IsHomogeneous (n + e)) (hy : y * x i ^ n = aeval x G) :
    φ y = c ^ e * ψ y := by sorry
