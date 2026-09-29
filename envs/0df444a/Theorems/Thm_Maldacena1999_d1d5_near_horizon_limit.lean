-- Prove2me | Theorems.Thm_Maldacena1999_d1d5_near_horizon_limit
-- name    : Maldacena1999.d1d5_near_horizon_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:11:58.612762+00:00
-- url     : https://prove2.me/theorems/b6d2bd4c-1882-424c-9c85-2ae74758250e
-- title:
--   D1–D5 decoupling limit, eq. (4.3): $ds^2/\alpha'\to\frac{U^2}{g_6\sqrt{Q_1Q_5}}dx^2+g_6\sqrt{Q_1Q_5}\left(\frac{dU^2}{U^2}+d\Omega_3^2\right)$
-- statement:
--   Let $g>0$ be the string coupling, $v>0$ the volume of $M^4$ in string units, and $Q_1,Q_5\ge1$ the numbers of D-strings and D5-branes. Consider the six-dimensional D1–D5 metric (4.2),
--   $$ds^2=f_1^{-1/2}f_5^{-1/2}\,dx_\parallel^2+f_1^{1/2}f_5^{1/2}\left(dr^2+r^2d\Omega_3^2\right),\qquad f_1=1+\frac{g\alpha'Q_1}{vr^2},\quad f_5=1+\frac{g\alpha'Q_5}{r^2},$$
--   with $dx_\parallel^2=-dt^2+dx^2$. Fix $U>0$, a point $\omega$ of the unit sphere $S^3\subset\mathbb R^4$, and a tangent vector $(\delta U,\delta x,\delta\omega)$ with $\delta x\in\mathbb R^{1,1}$ and $\delta\omega\perp\omega$. Evaluate the metric at $r=\alpha'U$ on the vector with radial component $\delta r=\alpha'\delta U$. With $g_6=g/\sqrt v$, as $\alpha'\to0^+$,
--   $$\frac{ds^2}{\alpha'}\;\longrightarrow\;\frac{U^2}{g_6\sqrt{Q_1Q_5}}\,\delta x^2+g_6\sqrt{Q_1Q_5}\,\frac{\delta U^2}{U^2}+g_6\sqrt{Q_1Q_5}\,\|\delta\omega\|^2 .$$
--
--   This is eq. (4.3): the near-horizon geometry of the D1–D5 system is $\mathrm{AdS}_3\times S^3$ with $R_{\rm sph}^2=\alpha' g_6\sqrt{Q_1Q_5}$.
--
--   **Formalization Note** Only the six-dimensional metric is modelled; the compact factor $M^4(Q)$ is omitted. Square roots of $f_1,f_5$ are `Real.rpow` with exponent $\pm1/2$.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://arxiv.org/abs/hep-th/9711200, pp. 1123-1125, Section 4, eqs. (4.1)-(4.3)

import Mathlib
import Definitions.Def_Maldacena1999_BraneDefs

open Filter Topology

namespace Maldacena1999

theorem d1d5_near_horizon_limit (g v : ℝ) (hg : 0 < g) (hv : 0 < v)
    (Q1 Q5 : ℕ) (hQ1 : 0 < Q1) (hQ5 : 0 < Q5) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 4)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 2 → ℝ) (δω : EuclideanSpace ℝ (Fin 4)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun α' : ℝ => d1d5Metric g v Q1 Q5 α' (α' * U) δx (α' * δU) δω / α')
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (g / Real.sqrt v * Real.sqrt (Q1 * Q5)) * minkowskiForm 1 δx +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * δU ^ 2 / U ^ 2 +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * ‖δω‖ ^ 2)) := by
  sorry

end Maldacena1999
