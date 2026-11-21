-- Prove2me | Theorems.Thm_NymanBeurling_real_certificate_has_rational_rounding
-- name    : NymanBeurling.real_certificate_has_rational_rounding
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T00:52:10.726877+00:00
-- url     : https://prove2.me/theorems/5294289c-ae8c-4697-871e-0546a843e53b
-- title:
--   Strict finite remainder certificates admit rational rounding without new denominators
-- statement:
--   For $k\ge0$ and $m\ge1$ let $r_k(m)=(m\bmod(k+2))/(k+2)$. Given $N,H\ge0$ and real coefficients $b_0,\ldots,b_{N-1}$, put
--
--   $$C_{N,H}(b)=\sum_{m=1}^{H}\frac{(1-\sum_{k=0}^{N-1}b_k r_k(m))^2}{m(m+1)}+\frac{(1+\sum_{k=0}^{N-1}|b_k|)^2}{H+1}.$$
--
--   If $C_{N,H}(b)<\eta$ for a real threshold $\eta$, then there is a finitely supported rational vector $c$ whose support is contained in $\{0,\ldots,N-1\}$ and whose rational certificate cost satisfies
--
--   $$C_H(c)<\eta.$$
--
--   The cutoff $H$ is preserved, and rounding introduces no new denominators. The assertion includes $N=0$ and $H=0$. It separates exact rational certification from the analytic construction of approximating real coefficients. The inequality must be strict; no assertion of preserving an equality threshold is made.
-- source:
--   Elementary continuity and rational-density lemma for the finite certificate frontier https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339 . The weighted norm comes from B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), Theorem 1, p. 137, https://arxiv.org/pdf/math/0607733 . The finite tail majorant and rational-rounding statement are explicit derived additions, not quotations from that paper.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.real_certificate_has_rational_rounding
    (N H : ℕ) (b : Fin N → ℝ) (η : ℝ)
    (h : (∑ n ∈ Finset.range H,
      (1 - ∑ k : Fin N, b k * (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) + (1 + ∑ k : Fin N, |b k|)^2/(H+1) < η) :
    ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
      (((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
        (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) : ℝ) < η := by sorry
