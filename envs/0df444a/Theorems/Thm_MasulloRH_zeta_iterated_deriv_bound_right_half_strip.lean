-- Prove2me | Theorems.Thm_MasulloRH_zeta_iterated_deriv_bound_right_half_strip
-- name    : MasulloRH.zeta_iterated_deriv_bound_right_half_strip
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T23:41:02.862382+00:00
-- url     : https://prove2.me/theorems/5b46c5c6-8df9-4644-b37c-30b58e2008e0
-- title:
--   Explicit Cauchy bounds for every zeta derivative on a right half-strip
-- statement:
--   For every integer order $r\ge0$ and every complex $s$ with $\Re s\ge1/2$ and $|\Im s|\ge2$,
--
--   $$|\zeta^{(r)}(s)|\le r!\,4^{r+1}(|s|+1).$$
--
--   Order zero denotes the function itself. There is no upper bound on the real part, and both signs of the imaginary part are included. The function is Mathlib’s actual Riemann zeta function; all points considered are away from its pole. The bound is unconditional and does not restrict the locations of zeros. It provides a uniform analytic remainder estimate for finite Taylor certificates, but does not establish nonvanishing.
-- source:
--   Original explicit certificate-support estimate for https://prove2.me/theorems/f9f6d44b-a148-4b98-8aa0-a911a4eaa8b4 . Uses the proved classical Euler–Maclaurin bound Zeta23.RvM.norm_riemannZeta_le_of_re_pos, https://prove2.me/theorems/f49f0c25-9fc8-49f9-b17c-64f059e1981d , and the Cauchy derivative estimate in Mathlib.Analysis.Complex.Liouville (Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474). No dependence on the Alpöge RH proof; no claim that the rectangle nonvanishing frontier is closed.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false

theorem MasulloRH.zeta_iterated_deriv_bound_right_half_strip (r : ℕ) (s : ℂ)
    (hsre : (1 / 2 : ℝ) ≤ s.re) (hsim : (2 : ℝ) ≤ |s.im|) :
    ‖iteratedDeriv r riemannZeta s‖ ≤
      (r.factorial : ℝ) * (4 * (‖s‖ + 1)) / (1 / 4 : ℝ) ^ r := by sorry
