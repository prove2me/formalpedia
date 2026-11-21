-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_limit_profile_tail_tightness
-- name    : NymanBeurling.damped_moebius_limit_profile_tail_tightness
-- status  : Open
-- author  : @pragyan
-- created : 2026-11-21T01:51:42.789805+00:00
-- url     : https://prove2.me/theorems/891fbda1-7a25-44bb-8617-840d92449dac
-- title:
--   Open uniform weighted tail tightness for the infinite damped Möbius profile
-- statement:
--   Here $R_{N,\varepsilon}(m)=1+\sum_{d=2}^{N+1}\mu(d)d^{-\varepsilon}(m\bmod d)/d$ and
--   $$P_\varepsilon(m)=1+m\sum_{d\ge1}\frac{\mu(d)}{d^{1+\varepsilon}}-\sum_{1\le d\le m}\frac{\mu(d)}{d^\varepsilon}\left\lfloor\frac{m}{d}\right\rfloor.$$
--   For every $\delta>0$, the proposed estimate asks for a coordinate cutoff $H_0\ge0$ and $0<\varepsilon_0\le1/2$ such that
--   $$\sum_{m=H_0+1}^{H}\frac{P_\varepsilon(m)^2}{m(m+1)}<\delta\qquad(0<\varepsilon<\varepsilon_0,\ H\ge0).$$
--   The cutoff is uniform as positive damping tends to zero. This open unconditional assertion concerns only the explicit infinite profile; the denominator cutoff $N$ has been removed. Together with weighted norm convergence of denominator truncations, it yields the iterated tail bound. Bagchi's second norm limit under RH implies this estimate, but no RH assumption is included here.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/pdf/math/0607733 , proof of Theorem 2 (i)⇒(ii), pp. 140–141: the second norm limit H_ε→E as ε decreases to zero, and proof of Theorem 1, p. 145: discrete sequence identification. This weaker uniform-tail formulation is a proposed unconditional open input derived from that RH-conditional construction, not an unconditional result quoted from the paper.

import Definitions.Def_NymanBeurling_DampedResidualLimits

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.damped_moebius_limit_profile_tail_tightness
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (H₀ : ℕ) (ε₀ : ℝ), 0 < ε₀ ∧ ε₀ ≤ 1/2 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ H : ℕ,
        (∑ n ∈ Finset.Ico H₀ H,
          (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
            ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by sorry
