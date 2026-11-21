-- Prove2me | Theorems.Thm_MasulloRH_regularized_trace_finite_height_error
-- name    : MasulloRH.regularized_trace_finite_height_error
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:36:07.704251+00:00
-- url     : https://prove2.me/theorems/5505d4c2-140b-4616-93e4-f72f75a9a20f
-- title:
--   Uniform finite-height error bound for Masullo’s regularized trace on the initial half-plane
-- statement:
--   Put $Z=\{\rho:\zeta(\rho)=0,\ 0<\Re\rho<1\}$ and let $m_\rho$ be the order of vanishing. For a real window half-width $\alpha$, a height $T$, and a complex test point $s$ with $\Re s>3/2$ and $|s|\le R$, write $O_\alpha=\{\rho\in Z:|\Re\rho-1/2|\ge\alpha\}$, $w_\rho=m_\rho/(1+(\Im\rho)^2)$, and $r_s(\rho)=m_\rho((s-\rho)^{-1}-(5/2-\rho)^{-1})$. Let $H_\alpha(s)$ denote Masullo’s regularized trace in that window. Then
--   $$\left|\frac{\zeta'}{\zeta}(s)-H_\alpha(s)-\sum_{\substack{\rho\in O_\alpha\\|\Im\rho|\le T}}r_s(\rho)\right|\le 2(2R+3)(R+5/2)\sum_{\substack{\rho\in O_\alpha\\|\Im\rho|> T}} w_\rho.$$
--   The weighted sum on the right is convergent. The constant works simultaneously for every such $s$, every height and every window, including a zero on the edge of the open window.
-- source:
--   A. M. Masullo, The Music of the Primes, 20 November 2026 frozen draft, §12.5.1, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . Quantitative estimate for the campaign’s explicitly regularized trace, using its proved full-strip identity and weighted zero summability.

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

namespace MasulloRH

theorem regularized_trace_finite_height_error (α T R : ℝ) (s : ℂ)
    (hR : ‖s‖ ≤ R) (hs : (3/2:ℝ) < s.re) :
    ‖(zetaLogDeriv s - regularizedTraceRHS α s) -
      (∑' z : ZetaZerosInTraceStrip (1/2),
        if α ≤ |z.val.re-1/2| ∧ |z.val.im| ≤ T then zeroResolventTerm (1/2) s z else 0)‖ ≤
      (2*(2*R+3)*(R+5/2)) * ∑' z : ZetaZerosInTraceStrip (1/2),
        if α ≤ |z.val.re-1/2| ∧ T < |z.val.im| then zeroDecayWeight (1/2) z else 0 := by sorry

end MasulloRH
