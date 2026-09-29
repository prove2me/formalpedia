-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_exp_I_mul_star_exp_I
-- name    : KobayashiMaskawa1973.exp_I_mul_star_exp_I
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:47:31.839198+00:00
-- url     : https://prove2.me/theorems/28589cfc-5bac-4683-a955-952b2be0e835
-- title:
--   Phase exponential times conjugate is 1
-- statement:
--   For any real number $t \in \mathbb{R}$, the complex phase $e^{it}$ satisfies:
--
--   $$e^{it} (e^{it})^* = e^{it} e^{-it} = 1.$$
-- source:
--   Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

import Mathlib

namespace KobayashiMaskawa1973

theorem exp_I_mul_star_exp_I (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) * star (Complex.exp ((t : ℂ) * Complex.I)) = 1 := by sorry

end KobayashiMaskawa1973
