-- Prove2me | Theorems.Thm_Maldacena1999_m2_near_horizon_limit
-- name    : Maldacena1999.m2_near_horizon_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:11:36.458509+00:00
-- url     : https://prove2.me/theorems/a21b85c3-2263-4b40-8a3a-02f077e9ff90
-- title:
--   M2-brane decoupling limit, Section 3.2: $\mathrm{AdS}_4\times S^7$ with $R_{\rm sph}=2R_{\rm AdS}=l_p(2^5\pi^2N)^{1/6}$
-- statement:
--   Let $N\ge1$ be the number of coincident M2-branes and consider the M2-brane metric (3.3),
--   $$ds^2=f^{-2/3}\,dx_\parallel^2+f^{1/3}\left(dr^2+r^2d\Omega_7^2\right),\qquad f=1+\frac{2^5\pi^2 N l_p^6}{r^6}.$$
--   Fix $U>0$, a point $\omega$ of the unit sphere $S^7\subset\mathbb R^8$, and a tangent vector $(\delta U,\delta x,\delta\omega)$ with $\delta x\in\mathbb R^{1,2}$ and $\delta\omega\perp\omega$. Evaluate the metric at $r=\sqrt{U l_p^3}$ (i.e. $U^{1/2}=r/l_p^{3/2}$) on the vector with radial component $\delta r=\dfrac{l_p^3}{2\sqrt{Ul_p^3}}\,\delta U$. Writing $K=2^5\pi^2N$, as $l_p\to0^+$,
--   $$\frac{ds^2}{l_p^2}\;\longrightarrow\;\frac{U^2}{K^{2/3}}\,\delta x^2+\frac{K^{1/3}}{4}\,\frac{\delta U^2}{U^2}+K^{1/3}\,\|\delta\omega\|^2 ,$$
--   where $\delta x^2=-\delta x_0^2+\delta x_1^2+\delta x_2^2$.
--
--   This is the statement of Section 3.2 that in the decoupling limit one obtains $\mathrm{AdS}_4\times S^7$ with $R_{\rm sph}=2R_{\rm AdS}=l_p(2^5\pi^2N)^{1/6}$: the coefficient of $\|\delta\omega\|^2$ is $R_{\rm sph}^2/l_p^2$ and that of $\delta U^2/U^2$ is $R_{\rm AdS}^2/l_p^2$.
--
--   **Formalization Note** The paper does not display the limit metric for the M2 case; the right-hand side above is the limit metric whose radii are the ones stated in the paper. Fractional powers are `Real.rpow`.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://arxiv.org/abs/hep-th/9711200, pp. 1122-1123, Section 3.2, eq. (3.3) and the radii below it

import Mathlib
import Definitions.Def_Maldacena1999_BraneDefs

open Filter Topology

namespace Maldacena1999

theorem m2_near_horizon_limit (N : ℕ) (hN : 0 < N) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 8)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 3 → ℝ) (δω : EuclideanSpace ℝ (Fin 8)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun lp : ℝ => m2Metric N lp (Real.sqrt (U * lp ^ 3)) δx
        (lp ^ 3 / (2 * Real.sqrt (U * lp ^ 3)) * δU) δω / lp ^ 2)
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (2 ^ 5 * Real.pi ^ 2 * N) ^ (2 / 3 : ℝ) * minkowskiForm 2 δx +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) / 4 * δU ^ 2 / U ^ 2 +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) * ‖δω‖ ^ 2)) := by
  sorry

end Maldacena1999
