-- Prove2me | Theorems.Thm_MasulloRH_exists_positive_log_profile_rank_discriminator
-- name    : MasulloRH.exists_positive_log_profile_rank_discriminator
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:18:41.725179+00:00
-- url     : https://prove2.me/theorems/47f46585-d134-434c-909e-0b58cfc6b201
-- title:
--   A positive-log-support test separates the weighted evaluation correction from the half-Mellin moment
-- statement:
--   There exists a real smooth compactly supported function u on the positive half-line with support contained in (1,32), whose absolutely convergent Mellin transforms at 1 and −1/2 both vanish, while the real part of its Mellin transform at 1/2 is strictly positive. The matched log-coordinate function f(s)=u(exp s) is smooth, compactly supported strictly in s>0, and satisfies ∫ℝ f(s)exp(−|s|/2)ds=0. The theorem separates this specific evaluation-correction functional from the scalar half-Mellin moment on the same test.
-- source:
--   Application to the weighted Paley–Wiener and finite prime-shell comparison in the Masullo RH mission. Finite scalar shell normalization: https://prove2.me/theorems/c2c832e0-37f7-48a3-9a12-809625c31683 . Context for the remaining indented diagonal comparison: https://github.com/mccorvie/riemann-masullo/issues/1358#issuecomment-7055141128 . The witness is constructed directly from Mathlib by two compact dilations and a change to logarithmic coordinates.

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.MellinTransform

open MeasureTheory Set

theorem MasulloRH.exists_positive_log_profile_rank_discriminator :
    ∃ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ioo 1 32 ∧
      HasMellin (fun t => (u t:ℂ)) 1 0 ∧ HasMellin (fun t => (u t:ℂ)) (-(1/2):ℂ) 0 ∧
      0 < (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re ∧
      (let f := fun s : ℝ => u (Real.exp s)
       ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi 0 ∧
       (∫ s : ℝ, f s * Real.exp (-|s|/2)) = 0) := by sorry
