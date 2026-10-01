-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_newton_local_order
-- name    : NonsmoothNewton.Local.newton_local_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:04:27.375704+00:00
-- url     : https://prove2.me/theorems/4b986089-b174-4a61-8257-71b56f1c4fe5
-- title:
--   Theorem 3.2 (second part) — convergence of order $1+p$
-- statement:
--   Let $F : \mathbb R^n \to \mathbb R^n$ be locally Lipschitz, let $x^*$ satisfy $F(x^*) = 0$, let $F$ be semismooth at $x^*$, and let every $V \in \partial F(x^*)$ be nonsingular. Suppose in addition that $0 < p \le 1$ and $F$ is $p$-order semismooth at $x^*$. Then there are $\delta > 0$ and a constant $C$ such that every run $(x^k, V_k)$ of the nonsmooth Newton method
--
--   $$
--   x^{k+1} = x^k - V_k^{-1}F(x^k), \qquad V_k \in \partial F(x^k),
--   $$
--
--   started at a point with $\|x^0 - x^*\| < \delta$ (for every choice of the $V_k$) satisfies
--
--   $$
--   \|x^{k+1} - x^*\| \le C\,\|x^k - x^*\|^{1+p} \qquad \text{for all } k \ge 0 .
--   $$
--
--   For $p = 1$ this is local quadratic convergence of the generalized-Jacobian Newton method.
--
--   **Formalization Note** The paper's "the convergence of (3.2) is of order $1+p$" is pinned as the displayed inequality, with $\delta$ and $C$ chosen before the run (uniform over all starting points and all choices of $V_k$), which is what the proof gives. A run is a sequence with $V_k \in \partial F(x^k)$ and $V_k(x^{k+1}-x^k) = -F(x^k)$.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 359, Theorem 3.2 (second sentence)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_NonsmoothNewton_Local_IsNewtonRun
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Theorem 3.2 (second sentence), p. 359. Under the hypotheses of Theorem 3.2,
if in addition `F` is `p`-order semismooth at `x*` (`0 < p ≤ 1`), the convergence of (3.2) is
of order `1 + p`: there are `δ > 0` and `C` such that every run started within `δ` of `x*`
satisfies `‖x^{k+1} - x*‖ ≤ C ‖x^k - x*‖^{1+p}` for all `k`. -/
theorem newton_local_order {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : F xstar = 0) (hsemi : SemismoothAt F xstar)
    (hns : ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F xstar, IsUnit V)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hpord : POrderSemismoothAt p F xstar) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (x : ℕ → EuclideanSpace ℝ (Fin n))
      (V : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ‖x 0 - xstar‖ < δ → IsNewtonRun F x V →
        ∀ k, ‖x (k + 1) - xstar‖ ≤ C * ‖x k - xstar‖ ^ (1 + p) := by sorry

end NonsmoothNewton.Local
