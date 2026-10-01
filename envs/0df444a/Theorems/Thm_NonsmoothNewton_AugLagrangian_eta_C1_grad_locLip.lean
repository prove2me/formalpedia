-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_eta_C1_grad_locLip
-- name    : NonsmoothNewton.AugLagrangian.eta_C1_grad_locLip
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:49:51.72999+00:00
-- url     : https://prove2.me/theorems/dd55bf70-a646-471c-98f9-108ed4585394
-- title:
--   Proof of Theorem 4.1: $\eta \in C^1$, the formula for $\nabla\eta$, and $\nabla\eta$ locally Lipschitz
-- statement:
--   Let $r > 0$ and let $g : \mathbb{R}^n \to \mathbb{R}$ be of class $C^2$. Put $\eta(x, s) = \phi(r, g(x), s)$, i.e.
--   $$
--   \eta(x,s) = \begin{cases} s\, g(x) + \tfrac12 r g(x)^2, & s + r g(x) \ge 0,\\ -\tfrac{1}{2r} s^2, & s + r g(x) \le 0.\end{cases}
--   $$
--   Then:
--   1. $\eta$ is continuously differentiable on $\mathbb{R}^n \times \mathbb{R}$;
--   2. its gradient is
--   $$
--   \nabla \eta(x, s) = \begin{cases} \begin{pmatrix} (s + r g(x)) \nabla g(x) \\ g(x) \end{pmatrix}, & s + r g(x) \ge 0,\\[6pt] \begin{pmatrix} 0 \\ -s/r \end{pmatrix}, & s + r g(x) \le 0; \end{cases}
--   $$
--   3. $\nabla \eta$ is locally Lipschitz.
--
--   This is the first step of the proof of Theorem 4.1: it establishes that each inequality term of the augmented Lagrangian is $C^1$ and that its gradient is regular enough (locally Lipschitz) for semismoothness to make sense.
--
--   **Formalization Note** The gradient is represented by the Fréchet derivative, a continuous linear functional on $\mathbb{R}^n \times \mathbb{R}$: in the first case $(h, \alpha) \mapsto (s + r g(x))\, Dg(x) h + g(x)\, \alpha$, in the second $(h, \alpha) \mapsto -(s/r)\, \alpha$. It corresponds to the gradient vector through the Riesz isometry.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), pp. 363–364, Section 4, proof of Theorem 4.1 (display of ∇η and the sentence after it)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Qi–Sun (1993), Section 4, proof of Theorem 4.1, pp. 363–364. For `r > 0` and `g ∈ C²`,
`η(x, s) = φ(r, g(x), s)` is `C¹`, its gradient is
`∇η(x, s) = ((s + r g(x)) ∇g(x), g(x))` if `s + r g(x) ≥ 0` and `(0, -s/r)` if
`s + r g(x) ≤ 0` (here as the Fréchet derivative, a linear functional on `ℝⁿ × ℝ`),
and `∇η` is locally Lipschitz. -/
theorem eta_C1_grad_locLip {n : ℕ} (r : ℝ) (hr : 0 < r) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 (eta r g) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, 0 ≤ z.2 + r * g z.1 →
      fderiv ℝ (eta r g) z =
        (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp
            (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
          + g z.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × ℝ, z.2 + r * g z.1 ≤ 0 →
      fderiv ℝ (eta r g) z =
        (-(z.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
    LocallyLipschitz (fun z => fderiv ℝ (eta r g) z) := by sorry

end NonsmoothNewton.AugLagrangian
