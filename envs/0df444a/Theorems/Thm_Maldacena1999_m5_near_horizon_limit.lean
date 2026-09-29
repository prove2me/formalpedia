-- Prove2me | Theorems.Thm_Maldacena1999_m5_near_horizon_limit
-- name    : Maldacena1999.m5_near_horizon_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:10:08.126136+00:00
-- url     : https://prove2.me/theorems/a54b960f-338d-4149-bfa1-ea9dbe264e73
-- title:
--   M5-brane decoupling limit, eq. (3.2): $ds^2/l_p^2\to \frac{U^2}{(\pi N)^{1/3}}dx^2+4(\pi N)^{2/3}\frac{dU^2}{U^2}+(\pi N)^{2/3}d\Omega_4^2$
-- statement:
--   Let $N\ge1$ be the number of coincident M5-branes and consider the M5-brane metric (3.1),
--   $$ds^2=f^{-1/3}\,dx_\parallel^2+f^{2/3}\left(dr^2+r^2d\Omega_4^2\right),\qquad f=1+\frac{\pi N l_p^3}{r^3}.$$
--   Fix $U>0$, a point $\omega$ of the unit sphere $S^4\subset\mathbb R^5$, and a tangent vector $(\delta U,\delta x,\delta\omega)$ with $\delta x\in\mathbb R^{1,5}$ and $\delta\omega\perp\omega$. Evaluate the metric at $r=U^2l_p^3$ on the vector with radial component $\delta r=2Ul_p^3\,\delta U$, the image of $\delta U$ under $U\mapsto r=U^2l_p^3$. Then, as $l_p\to0^+$,
--   $$\frac{ds^2}{l_p^2}\;\longrightarrow\;\frac{U^2}{(\pi N)^{1/3}}\,\delta x^2+4(\pi N)^{2/3}\,\frac{\delta U^2}{U^2}+(\pi N)^{2/3}\,\|\delta\omega\|^2 ,$$
--   where $\delta x^2=-\delta x_0^2+\delta x_1^2+\dots+\delta x_5^2$.
--
--   This is eq. (3.2): in the decoupling limit with $U^2=r/l_p^3$ fixed, the metric in Planck units is $\mathrm{AdS}_7\times S^4$ with $R_{\rm sph}=R_{\rm AdS}/2=l_p(\pi N)^{1/3}$.
--
--   **Formalization Note** Fractional powers are `Real.rpow`. The sphere metric is the Euclidean norm of a tangent vector to the unit sphere in $\mathbb R^5$.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://arxiv.org/abs/hep-th/9711200, p. 1122, Section 3.1, eqs. (3.1)-(3.2)

import Mathlib
import Definitions.Def_Maldacena1999_BraneDefs

open Filter Topology

namespace Maldacena1999

theorem m5_near_horizon_limit (N : ℕ) (hN : 0 < N) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 5)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 6 → ℝ) (δω : EuclideanSpace ℝ (Fin 5)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun lp : ℝ => m5Metric N lp (U ^ 2 * lp ^ 3) δx (2 * U * lp ^ 3 * δU) δω / lp ^ 2)
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (Real.pi * N) ^ (1 / 3 : ℝ) * minkowskiForm 5 δx +
        4 * (Real.pi * N) ^ (2 / 3 : ℝ) * δU ^ 2 / U ^ 2 +
        (Real.pi * N) ^ (2 / 3 : ℝ) * ‖δω‖ ^ 2)) := by
  sorry

end Maldacena1999
