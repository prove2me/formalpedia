-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_step_lower_bound_armijo
-- name    : NonmonotoneLS.Global.step_lower_bound_armijo
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:24:29.152634+00:00
-- url     : https://prove2.me/theorems/47cb4260-a330-47e6-b265-5ab7e48d9879
-- title:
--   Lemma 2.1 (Armijo case) — lower bound (2.2) on the Armijo step
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable, let the NLSA parameters be fixed, and let $x, d \in \mathbb{R}^n$, $C \in \mathbb{R}$ and $L > 0$. Write $g = \nabla f(x)$. Suppose $g^{\mathsf T} d \le 0$, $f(x) \le C$, the step $\alpha$ satisfies the nonmonotone Armijo conditions at $x$ with direction $d$ and reference value $C$, and, if $\rho\alpha \le \mu$,
--
--   $$\|\nabla f(y) - \nabla f(x)\| \le L\|y - x\| \quad \text{for all } y \text{ on the segment from } x \text{ to } x + \alpha\rho d.$$
--
--   Then
--
--   $$\alpha \ge \min\left\{ \frac{\mu}{\rho},\ \left(\frac{2(1-\delta)}{L\rho}\right) \frac{|g^{\mathsf T} d|}{\|d\|^2} \right\}. \qquad (2.2)$$
--
--   Together with (2.1), this bound gives the uniform sufficient decrease (2.8) behind Theorem 2.2.
--
--   **Formalization Note.** The statement is for one iteration ($x = x_k$, $d = d_k$, $C = C_k$). The hypothesis $f(x) \le C$ is the fact "$f_k \le C_k$" that the paper's proof invokes; along a run it is supplied by Lemma 1.1, and it is made explicit because the statement is pointwise. At $d = 0$ Lean's division by zero makes the second entry of the minimum $0$, which is harmless.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1046, Lemma 2.1, Eq. (2.2)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Lemma 2.1, Armijo case (p. 1046), Eq. (2.2): if `∇f(x) d ≤ 0`, `f(x) ≤ C`, `α` satisfies the
nonmonotone Armijo conditions at `(x, d, C)`, and, when `ρ α ≤ μ`,
`‖∇f(y) - ∇f(x)‖ ≤ L ‖y - x‖` for every `y` on the segment from `x` to `x + α ρ d`, then
`α ≥ min{μ/ρ, (2(1 - δ)/(L ρ)) |∇f(x) d| / ‖d‖²}`. -/
theorem step_lower_bound_armijo {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ) (hL : 0 < L)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0) (hfC : f x ≤ C)
    (hstep : Shared.IsArmijoStep p f x d C α)
    (hLip : p.ρ * α ≤ p.μ → ∀ y ∈ segment ℝ x (x + (p.ρ * α) • d),
      ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖) :
    min (p.μ / p.ρ)
        (2 * (1 - p.δ) / (L * p.ρ) * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2)) ≤ α := by sorry

end NonmonotoneLS.Global
