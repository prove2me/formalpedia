-- Prove2me | Theorems.Thm_LL_TailNegMainTerm_main_term_envelope_near_real
-- name    : LL_TailNegMainTerm.main_term_envelope_near_real
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-24T17:22:30.983394+00:00
-- url     : https://prove2.me/theorems/6fe11a49-45c7-421f-a66c-1b417b8046a2
-- title:
--   Stirling main term envelope at $5/2+it$ for $2\le t\le 5/2$
-- statement:
--   For every real $t$ with $2\le t\le 5/2$, put $w=5/2+it$ and $L=\log\sqrt{25/4+t^2}+i\arcsin\bigl(t/\sqrt{25/4+t^2}\bigr)$. Then
--   $$\Bigl|L-\frac{1}{2w}-\frac{1}{12w^2}-\Bigl(\frac{1}{-1/2+it}+\frac{1}{1/2+it}+\frac{1}{3/2+it}\Bigr)\Bigr|+\frac{2}{9375}\le\log t+\frac32.$$
-- source:
--   Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, page 34, display 4.10, near range; Lean Lab split of the gamma factor envelope.

import Mathlib

namespace LL_TailNegMainTerm
open Complex

theorem main_term_envelope_near_real (t : ℝ) (ht : 2 ≤ t) (ht' : t ≤ 5 / 2) :
    ‖((Real.log (Real.sqrt (25 / 4 + t ^ 2)) : ℝ) : ℂ) +
          ((Real.arcsin (t / Real.sqrt (25 / 4 + t ^ 2)) : ℝ) : ℂ) * I -
          1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log t + 3 / 2 := by sorry
end LL_TailNegMainTerm
