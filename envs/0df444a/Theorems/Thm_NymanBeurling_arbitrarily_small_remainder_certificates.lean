-- Prove2me | Theorems.Thm_NymanBeurling_arbitrarily_small_remainder_certificates
-- name    : NymanBeurling.arbitrarily_small_remainder_certificates
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T00:30:07.656456+00:00
-- url     : https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339
-- title:
--   Arbitrarily small finite rational certificates for Bagchi’s discrete approximation criterion
-- statement:
--   For positive integers $m$ set $r_k(m)=(m\bmod(k+2))/(k+2)$ and take a finitely supported rational vector $c$. Its residual is $e_c(m)=1-\sum_k c_k r_k(m)$. For an integer cutoff $H\ge0$ define the rational certificate cost
--   $$C_H(c)=\sum_{m=1}^H\frac{e_c(m)^2}{m(m+1)}+\frac{(1+\sum_k |c_k|)^2}{H+1}.$$
--   The last term bounds the whole omitted tail by telescoping.
--   For each natural number $J$, there exist $c,H$ with $C_H(c)<1/(J+1)$. This is the open approximation assertion in the discrete Nyman–Beurling approach. Its truth would imply the Riemann hypothesis. For fixed $c,H,J$ all values and the comparison are finite rational arithmetic. Bagchi's Hilbert-space criterion uses the exact infinite weighted norm. Rational coefficient approximation on a finite span and letting the tail majorant tend to zero recover this finite-certificate formulation.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146, Theorems 1 and 2 and the Mellin identity (4). https://arxiv.org/abs/math/0607733. The finite rational tail majorant is an elementary explicit addition.

import Mathlib

set_option autoImplicit false

theorem NymanBeurling.arbitrarily_small_remainder_certificates (J : ℕ) :
    ∃ (c : ℕ →₀ ℚ) (H : ℕ), ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1/(J+1 : ℚ) := by sorry
