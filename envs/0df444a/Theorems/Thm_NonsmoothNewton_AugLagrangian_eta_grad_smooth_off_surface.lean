-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_eta_grad_smooth_off_surface
-- name    : NonsmoothNewton.AugLagrangian.eta_grad_smooth_off_surface
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:51:18.690808+00:00
-- url     : https://prove2.me/theorems/de391d5d-5c94-42ce-890c-a796a50ff00c
-- title:
--   Eq. (4.2): the Hessian of $\eta$ off the surface $s + r g(x) = 0$, where $\nabla\eta$ is smooth
-- statement:
--   Let $r > 0$, let $g : \mathbb{R}^n \to \mathbb{R}$ be of class $C^2$, and let $\eta(x, s) = \phi(r, g(x), s)$. Then
--   $$
--   \nabla^2 \eta(x, s) = \begin{cases} \begin{pmatrix} r \nabla g(x) \nabla g(x)^{\mathsf T} + (s + r g(x)) \nabla^2 g(x) & \nabla g(x) \\ \nabla g(x)^{\mathsf T} & 0 \end{pmatrix}, & s + r g(x) > 0,\\[10pt] \begin{pmatrix} 0 & 0 \\ 0 & -1/r \end{pmatrix}, & s + r g(x) < 0, \end{cases} \tag{4.2}
--   $$
--   and $\nabla \eta$ is continuously differentiable in a neighbourhood of every point $(x, s)$ with $s + r g(x) \neq 0$.
--
--   That is, $\nabla\eta$ is smooth except on the surface $s + r g(x) = 0$; the remaining work of Theorem 4.1 is semismoothness on that surface.
--
--   **Formalization Note** The Hessian is the Fréchet derivative of the map $(x, s) \mapsto D\eta(x, s)$. Applied to a direction $(h, \alpha)$ it is stated as the linear functional $(k, \beta) \mapsto (r\, Dg(x)h + \alpha)\, Dg(x)k + (s + r g(x))\, D^2 g(x)(h, k) + Dg(x)h\, \beta$ when $s + r g(x) > 0$, and $(k, \beta) \mapsto -(\alpha / r)\,\beta$ when $s + r g(x) < 0$, which is the matrix (4.2) applied to $(h, \alpha)$ and paired with $(k, \beta)$. "Smooth" is the paper's continuously differentiable (`ContDiffAt ℝ 1`).
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 364, Section 4, Eq. (4.2) and the sentence after it

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Qi–Sun (1993), Section 4, Eq. (4.2), p. 364. For `r > 0` and `g ∈ C²`, the Hessian of
`η(x, s) = φ(r, g(x), s)` is, applied to a direction `(h, α)`,
`(r ∇g(x)∇g(x)ᵀ + (s + r g(x)) ∇²g(x)) h + α ∇g(x)` in `x` and `∇g(x)ᵀ h` in `s` where
`s + r g(x) > 0`, and `(0, -α/r)` where `s + r g(x) < 0`; and `∇η` is `C¹` near every point
off the surface `s + r g(x) = 0`. -/
theorem eta_grad_smooth_off_surface {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g) :
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, 0 < z.2 + r * g z.1 →
      ∀ v : EuclideanSpace ℝ (Fin n) × ℝ,
        fderiv ℝ (fun w => fderiv ℝ (eta r g) w) z v =
          (r * fderiv ℝ g z.1 v.1 + v.2) • (fderiv ℝ g z.1).comp
              (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
            + (z.2 + r * g z.1) • (fderiv ℝ (fun u => fderiv ℝ g u) z.1 v.1).comp
              (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
            + fderiv ℝ g z.1 v.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, z.2 + r * g z.1 < 0 →
      ∀ v : EuclideanSpace ℝ (Fin n) × ℝ,
        fderiv ℝ (fun w => fderiv ℝ (eta r g) w) z v =
          (-(v.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, z.2 + r * g z.1 ≠ 0 →
      ContDiffAt ℝ 1 (fun w => fderiv ℝ (eta r g) w) z) := by sorry

end NonsmoothNewton.AugLagrangian
