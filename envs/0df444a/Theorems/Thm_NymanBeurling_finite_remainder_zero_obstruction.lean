-- Prove2me | Theorems.Thm_NymanBeurling_finite_remainder_zero_obstruction
-- name    : NymanBeurling.finite_remainder_zero_obstruction
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:30:06.701657+00:00
-- url     : https://prove2.me/theorems/91a803ad-ec78-40df-a6b3-a7318f64e145
-- title:
--   A finite rational remainder certificate excludes zeta zeros in an explicit disk
-- statement:
--   For positive integers $m$ set $r_k(m)=(m\bmod(k+2))/(k+2)$ and take a finitely supported rational vector $c$. Its residual is $e_c(m)=1-\sum_k c_k r_k(m)$. For an integer cutoff $H\ge0$ define the rational certificate cost
--   $$C_H(c)=\sum_{m=1}^H\frac{e_c(m)^2}{m(m+1)}+\frac{(1+\sum_k |c_k|)^2}{H+1}.$$
--   The last term bounds the whole omitted tail by telescoping.
--   If $\zeta(s)=0$, $s\ne1$, and $\Re s>1/2$, then $2\Re s-1\le C_H(c)|s|^2$ for every certificate. In particular, a specific finite calculation with $C_H(c)|s|^2<2\Re s-1$ certifies that $\zeta(s)\ne0$. The inequality itself holds unconditionally.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146, Theorems 1 and 2 and the Mellin identity (4). https://arxiv.org/abs/math/0607733. The finite rational tail majorant is an elementary explicit addition.

import Mathlib

set_option autoImplicit false

theorem NymanBeurling.finite_remainder_zero_obstruction (s : ℂ) (hs : 1 / 2 < s.re) (h1 : s ≠ 1)
    (hz : riemannZeta s = 0) (c : ℕ →₀ ℚ) (H : ℕ) :
    2*s.re-1 ≤ (((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) : ℝ) * ‖s‖^2 := by sorry
