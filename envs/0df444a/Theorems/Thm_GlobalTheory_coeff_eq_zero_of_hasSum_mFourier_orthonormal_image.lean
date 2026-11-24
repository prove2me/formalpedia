-- Prove2me | Theorems.Thm_GlobalTheory_coeff_eq_zero_of_hasSum_mFourier_orthonormal_image
-- name    : GlobalTheory.coeff_eq_zero_of_hasSum_mFourier_orthonormal_image
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:34.89569+00:00
-- url     : https://prove2.me/theorems/417fbb9b-f26c-46f9-aedc-4d3b29ebe901
-- title:
--   Global Theory: coeff eq zero of has Sum m Fourier orthonormal image
-- statement:
--   The Global Theory construction uses the coeff eq zero of has Sum m Fourier orthonormal image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffEqZeroOfHasSumMFourierOrthonormalImage.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffEqZeroOfHasSumMFourierOrthonormalImage.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory

theorem GlobalTheory.coeff_eq_zero_of_hasSum_mFourier_orthonormal_image {J : Type} [Fintype J] {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : C(UnitAddTorus J, ℂ) →L[ℂ] E)
    (hL : Orthonormal ℂ (fun n : J → ℤ => L (UnitAddTorus.mFourier n))) (b : (J → ℤ) → ℂ)
    (h : HasSum (fun s => b s • UnitAddTorus.mFourier s) (0 : C(UnitAddTorus J, ℂ)))
    (t : J → ℤ) : b t = 0 := by sorry
