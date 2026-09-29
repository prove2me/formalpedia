-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_eta_grad_semismooth_on_surface
-- name    : NonsmoothNewton.AugLagrangian.eta_grad_semismooth_on_surface
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:52:44.272342+00:00
-- url     : https://prove2.me/theorems/9ae14863-b5dc-48b9-b966-b7abb3085adc
-- title:
--   Proof of Theorem 4.1: $\nabla\eta$ is semismooth at every point of the surface $s + r g(x) = 0$
-- statement:
--   Let $r > 0$, let $g : \mathbb{R}^n \to \mathbb{R}$ be of class $C^2$, and let $\eta(x, s) = \phi(r, g(x), s)$. If $(\bar x, \bar s)$ satisfies
--   $$
--   \bar s + r g(\bar x) = 0, \tag{4.3}
--   $$
--   then $\nabla \eta$, as a map of $(x, s) \in \mathbb{R}^{n+1}$, is semismooth at $(\bar x, \bar s)$: it is locally Lipschitz there and, for every $(h, \alpha) \in \mathbb{R}^{n+1}$, the limit
--   $$
--   \lim_{\substack{h' \to h,\ \alpha' \to \alpha \\ t \downarrow 0}} \Big\{ V \begin{pmatrix} h' \\ \alpha' \end{pmatrix} : V \in \partial \nabla \eta(\bar x + t h', \bar s + t \alpha') \Big\} \tag{4.4}
--   $$
--   exists.
--
--   This is the nonsmooth heart of Theorem 4.1: on the surface where the two formulas for $\phi$ meet, $\nabla\eta$ is not differentiable, yet it is semismooth, which is what the nonsmooth Newton method requires.
--
--   **Formalization Note** $\nabla\eta$ is the Fréchet derivative map $(x,s) \mapsto D\eta(x,s)$, valued in linear functionals on $\mathbb{R}^n \times \mathbb{R}$; semismoothness is invariant under the Riesz isometry between functionals and gradient vectors and under the choice of equivalent norm on $\mathbb{R}^n \times \mathbb{R}$ (Mathlib's product carries the sup norm). The semismoothness is joint in $(x, s)$.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), pp. 364–365, Section 4, proof of Theorem 4.1, Eqs. (4.3)–(4.4) and the conclusion on p. 365

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Qi–Sun (1993), Section 4, proof of Theorem 4.1, pp. 364–365. For `r > 0` and `g ∈ C²`, the
gradient of `η(x, s) = φ(r, g(x), s)` is semismooth (jointly in `(x, s)`) at every point
`(x̄, s̄)` of the surface `s̄ + r g(x̄) = 0`. -/
theorem eta_grad_semismooth_on_surface {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (xbar : EuclideanSpace ℝ (Fin n)) (sbar : ℝ) (h43 : sbar + r * g xbar = 0) :
    SemismoothAt (fun w => fderiv ℝ (eta r g) w) (xbar, sbar) := by sorry

end NonsmoothNewton.AugLagrangian
