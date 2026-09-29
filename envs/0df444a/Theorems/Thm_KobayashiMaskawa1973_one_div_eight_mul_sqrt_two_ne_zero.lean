-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_one_div_eight_mul_sqrt_two_ne_zero
-- name    : KobayashiMaskawa1973.one_div_eight_mul_sqrt_two_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:28:55.1459+00:00
-- url     : https://prove2.me/theorems/d9cc829a-1f64-4828-a483-38b5a623532c
-- title:
--   1 / (8 * sqrt 2) is non-zero
-- statement:
--   The real number $\frac{1}{8\sqrt{2}}$ is strictly positive, and in particular is non-zero:
--
--   $$\frac{1}{8\sqrt{2}} \neq 0.$$
-- source:
--   Mathlib.Data.Real.Basic

import Mathlib

namespace KobayashiMaskawa1973

theorem one_div_eight_mul_sqrt_two_ne_zero :
    (1 / (8 * Real.sqrt 2) : ℝ) ≠ 0 := by sorry

end KobayashiMaskawa1973
