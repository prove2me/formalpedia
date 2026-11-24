-- Prove2me | Theorems.Thm_GlobalTheory_mFourier_coe_eq_exp
-- name    : GlobalTheory.mFourier_coe_eq_exp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:09:23.871652+00:00
-- url     : https://prove2.me/theorems/4028df9d-abe4-4c86-b58f-5d23d2d7db0a
-- title:
--   Global Theory: m Fourier coe eq exp
-- statement:
--   The Global Theory construction uses the m Fourier coe eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffEqZeroOfHasSumMFourierOrthonormalImage.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffEqZeroOfHasSumMFourierOrthonormalImage.lean#L25-L33

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

theorem GlobalTheory.mFourier_coe_eq_exp {J : Type} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    UnitAddTorus.mFourier s (fun j => (x j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) := by sorry
