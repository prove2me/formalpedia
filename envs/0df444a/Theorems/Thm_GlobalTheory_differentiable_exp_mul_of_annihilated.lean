-- Prove2me | Theorems.Thm_GlobalTheory_differentiable_exp_mul_of_annihilated
-- name    : GlobalTheory.differentiable_exp_mul_of_annihilated
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:55.648794+00:00
-- url     : https://prove2.me/theorems/1d1fe3e0-74ff-4686-bef4-7786bb8a7992
-- title:
--   Global Theory: differentiable exp mul of annihilated
-- statement:
--   The Global Theory construction uses the differentiable exp mul of annihilated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/DifferentiableExpMulOfAnnihilated.lean#L8-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/DifferentiableExpMulOfAnnihilated.lean#L8-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DifferentiableExpMulOfAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open Matrix

theorem GlobalTheory.differentiable_exp_mul_of_annihilated :
    ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by sorry
