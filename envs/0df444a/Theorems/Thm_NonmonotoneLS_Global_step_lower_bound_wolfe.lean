-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_step_lower_bound_wolfe
-- name    : NonmonotoneLS.Global.step_lower_bound_wolfe
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:23:40.866906+00:00
-- url     : https://prove2.me/theorems/dcd358e8-73b7-4283-ae9f-eef267fe022c
-- title:
--   Lemma 2.1 (Wolfe case) — lower bound (2.1) on the Wolfe step
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable, let the NLSA parameters be fixed, and let $x, d \in \mathbb{R}^n$, $C \in \mathbb{R}$ and $L > 0$. Write $g = \nabla f(x)$. Suppose $g^{\mathsf T} d \le 0$, the step $\alpha$ satisfies the nonmonotone Wolfe conditions (1.4)–(1.5) at $x$ with direction $d$ and reference value $C$, and
--
--   $$\|\nabla f(x + \alpha d) - \nabla f(x)\| \le L \|(x + \alpha d) - x\|.$$
--
--   Then
--
--   $$\alpha \ge \left(\frac{1-\sigma}{L}\right) \frac{|g^{\mathsf T} d|}{\|d\|^2}. \qquad (2.1)$$
--
--   This lower bound on accepted Wolfe steps is what converts the sufficient decrease condition (1.4) into a decrease proportional to $\|g\|^2$ in the proof of Theorem 2.2.
--
--   **Formalization Note.** The statement is for one iteration ($x = x_k$, $d = d_k$, $x + \alpha d = x_{k+1}$). At $d = 0$ Lean's division by zero makes the right-hand side $0$, which is harmless (the paper tacitly has $d_k \ne 0$). The Lipschitz constant is required positive, since it is a divisor; a Lipschitz constant can always be enlarged.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1046, Lemma 2.1, Eq. (2.1)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Lemma 2.1, Wolfe case (p. 1046), Eq. (2.1): if `∇f(x) d ≤ 0`, `α` satisfies the nonmonotone
Wolfe conditions at `(x, d, C)` and `‖∇f(x + α d) - ∇f(x)‖ ≤ L ‖(x + α d) - x‖`, then
`α ≥ ((1 - σ)/L) |∇f(x) d| / ‖d‖²`. -/
theorem step_lower_bound_wolfe {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ) (hL : 0 < L)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0)
    (hstep : Shared.IsWolfeStep p f x d C α)
    (hLip : ‖gradient f (x + α • d) - gradient f x‖ ≤ L * ‖(x + α • d) - x‖) :
    (1 - p.σ) / L * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2) ≤ α := by sorry

end NonmonotoneLS.Global
