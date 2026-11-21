-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_truncation_mean_square_convergence
-- name    : NymanBeurling.damped_moebius_truncation_mean_square_convergence
-- status  : Open
-- author  : @pragyan
-- created : 2026-11-21T01:51:41.725521+00:00
-- url     : https://prove2.me/theorems/b5d23ede-9bcc-4d2a-9c23-84182e886efc
-- title:
--   Open weighted norm convergence of damped Möbius denominator truncations
-- statement:
--   Fix $0<\varepsilon<1/2$. The proposed estimate asserts that for every $\delta>0$ there is $N_0$ such that
--   $$\sum_{m=1}^{H}\frac{(R_{N,\varepsilon}(m)-P_\varepsilon(m))^2}{m(m+1)}<\delta\qquad(N\ge N_0,\ H\ge0).$$
--   Here $R_{N,\varepsilon}(m)=1+\sum_{d=2}^{N+1}\mu(d)d^{-\varepsilon}(m\bmod d)/d$ and
--   $$P_\varepsilon(m)=1+m\sum_{d\ge1}\frac{\mu(d)}{d^{1+\varepsilon}}-\sum_{1\le d\le m}\frac{\mu(d)}{d^\varepsilon}\left\lfloor\frac{m}{d}\right\rfloor.$$
--   This is an open unconditional analytic obligation. It isolates the first, fixed-damping limit from the later limit as damping vanishes. Pointwise convergence follows from absolute convergence at $1+\varepsilon$; the unresolved requirement here is convergence in the weighted Hilbert norm. Bagchi proves the corresponding norm convergence assuming RH, which is not assumed in this statement.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/pdf/math/0607733 , proof of Theorem 2 (i)⇒(ii), p. 140: fixed-ε norm convergence H_{L,ε}→H_ε, and proof of Theorem 1, p. 145: discrete Hilbert-space identification. This is the explicit-sequence, unconditional open obligation extracted from that RH-conditional argument; the source does not prove it unconditionally.

import Definitions.Def_NymanBeurling_DampedResidualLimits

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.damped_moebius_truncation_mean_square_convergence
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
      (∑ n ∈ Finset.range H,
        (NymanBeurling.dampedResidualFinite N ε (n+1) -
          NymanBeurling.dampedResidualProfile ε (n+1))^2 /
            ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by sorry
