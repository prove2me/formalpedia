-- Prove2me | Theorems.Thm_Maldacena1999_near_horizon_limit_AdS5_S5
-- name    : Maldacena1999.near_horizon_limit_AdS5_S5
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:57:48.809337+00:00
-- url     : https://prove2.me/theorems/68eaa3f7-6c6b-49d2-a6c5-ecc77ea8c7f9
-- title:
--   Near-horizon limit of $N$ D3-branes is $\mathrm{AdS}_5\times S^5$ with $R^4=4\pi gN$
-- statement:
--   Let $g>0$ be the string coupling, $N\ge1$ the number of D3-branes, and let $R>0$ satisfy
--   $$R^4=4\pi gN .$$
--   Consider the D3-brane metric (2.2), $ds^2=f^{-1/2}dx_\parallel^2+f^{1/2}(dr^2+r^2d\Omega_5^2)$ with $f=1+4\pi gN\alpha'^2/r^4$, and pass to the variable $U=r/\alpha'$ of the decoupling limit (2.1), so that a tangent vector $(\delta x,\delta U,\delta\omega)$ has radial component $\delta r=\alpha'\delta U$. Fix $U>0$, $x\in\mathbb R^{1,3}$, a point $\omega$ of the unit sphere $S^5\subset\mathbb R^6$ and a tangent vector with $\delta\omega\perp\omega$. Then
--   $$\lim_{\alpha'\to0^+}\frac{ds^2_{\alpha'}\big|_{r=\alpha'U}(\delta x,\alpha'\delta U,\delta\omega)}{\alpha'}
--   =\big\langle d\Phi_R(U,x)[\delta U,\delta x],\,d\Phi_R(U,x)[\delta U,\delta x]\big\rangle_\eta+\|R\,\delta\omega\|^2 ,$$
--   where $\Phi_R$ is the Poincaré parametrisation (A.2) of $\mathrm{AdS}_5(R)\subset\mathbb R^{2,4}$ and $\langle\cdot,\cdot\rangle_\eta$ the flat metric of $\mathbb R^{2,4}$.
--
--   In words: after removing the overall factor $\alpha'$, the near-horizon limit of the D3-brane geometry is the metric induced on $\mathrm{AdS}_5$ of radius $R$ (in Poincaré coordinates) plus the round metric of a five-sphere of the same radius $R$, with $R^2=\sqrt{4\pi gN}$, i.e. eq. (2.3): $ds^2=\alpha'\big[\tfrac{U^2}{\sqrt{4\pi gN}}dx_\parallel^2+\sqrt{4\pi gN}\tfrac{dU^2}{U^2}+\sqrt{4\pi gN}\,d\Omega_5^2\big]$.
--
--   This is the geometric statement underlying the paper's identification of the decoupled D3-brane geometry with $\mathrm{AdS}_5\times S^5$.
--
--   **Formalization Note** The limit is taken pointwise for each fixed tangent vector, along $\alpha'\to0^+$. The induced AdS metric is expressed through the Fréchet derivative of the Poincaré parametrisation. The point $x$, the point $\omega$ and the tangency of $\delta\omega$ are kept to match the geometric setting even though the metric coefficients do not depend on them.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Section 2, eqs. (2.1)-(2.3), p. 1115-1116, together with Appendix eq. (A.3), p. 1130

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

namespace Maldacena1999

theorem near_horizon_limit_AdS5_S5 (g : ℝ) (hg : 0 < g) (N : ℕ) (hN : 0 < N)
    (R : ℝ) (hR : 0 < R) (hR4 : R ^ 4 = 4 * Real.pi * g * N)
    (U : ℝ) (hU : 0 < U) (x : Fin 4 → ℝ)
    (ω : EuclideanSpace ℝ (Fin 6)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 4 → ℝ) (δω : EuclideanSpace ℝ (Fin 6)) (hδω : inner ℝ ω δω = 0) :
    Tendsto (fun α' : ℝ => d3Metric g N α' (α' * U) δx (α' * δU) δω / α') (𝓝[>] 0)
      (𝓝 (ambientForm 3 (fderiv ℝ (poincareEmbedding 3 R) (U, x) (δU, δx)) +
        ‖R • δω‖ ^ 2)) := by
  sorry

end Maldacena1999
