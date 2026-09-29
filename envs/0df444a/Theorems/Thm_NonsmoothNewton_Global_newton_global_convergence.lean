-- Prove2me | Theorems.Thm_NonsmoothNewton_Global_newton_global_convergence
-- name    : NonsmoothNewton.Global.newton_global_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:11:10.607202+00:00
-- url     : https://prove2.me/theorems/36a2bb99-6269-4b07-9c38-e8f56cd5140e
-- title:
--   Theorem 3.3 (global convergence) — the nonsmooth Newton iterates stay in $S$ and converge to the unique zero of $F$ in $S$, with error estimate (3.4)
-- statement:
--   Let $F : \mathbb{R}^n \to \mathbb{R}^n$ be locally Lipschitz, $x^0 \in \mathbb{R}^n$, $r \ge 0$, and $S = \{x \in \mathbb{R}^n : \|x - x^0\| \le r\}$ with the Euclidean norm. Write $\partial F$ for Clarke's generalized Jacobian and $F'(x;h)$ for the one-sided directional derivative. Suppose:
--
--   1. $F$ is semismooth at every point of $S$;
--   2. for all $x \in S$, every $V \in \partial F(x)$ is nonsingular and $\|V^{-1}\| \le \beta$;
--   3. for all $x, y \in S$ and all $V \in \partial F(x)$,
--   $$\|V(y - x) - F'(x; y - x)\| \le \gamma\|y - x\|;$$
--   4. for all $x, y \in S$,
--   $$\|F(y) - F(x) - F'(x; y - x)\| \le \delta\|y - x\|;$$
--   5. $\alpha = \beta(\gamma + \delta) < 1$ and $\beta\|F(x^0)\| \le r(1 - \alpha)$.
--
--   Let $(x^k, V_k)_{k\ge0}$ be any run of the nonsmooth Newton method (3.2) started at $x^0$: $V_k \in \partial F(x^k)$ and $x^{k+1} = x^k - V_k^{-1}F(x^k)$. Then every $x^k$ lies in $S$ and every $V_k$ is nonsingular; $F$ has a unique zero $x^*$ in $S$; $x^k \to x^*$; and for $k = 1, 2, \dots$
--
--   $$
--   \|x^k - x^*\| \le \frac{\alpha}{1-\alpha}\,\|x^k - x^{k-1}\|. \tag{3.4}
--   $$
--
--   This is a nonsmooth extension of the Newton–Kantorovich theorem: it guarantees a solution in a prescribed ball, its uniqueness there, and an a-posteriori error bound computable from consecutive iterates.
--
--   **Formalization Note** The run is a relation $V_k(x^{k+1} - x^k) = -F(x^k)$ with $V_k\in\partial F(x^k)$; nonsingularity of each $V_k$ is part of the conclusion. $\|V^{-1}\| \le \beta$ is the existence of a two-sided inverse of operator norm at most $\beta$. The radius condition $r \ge 0$ is explicit. Hypothesis 4 is stated without the quantifier "for any $V \in \partial F(x)$" that the paper's sentence places over all three inequalities; since $\partial F(x) \neq \emptyset$ for locally Lipschitz $F$, the two readings coincide. (3.4) is stated with index $k+1$ for $k \ge 0$, avoiding natural-number subtraction.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 359, Theorem 3.3 (proof p. 360)

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- **Theorem 3.3 (global convergence)** of Qi–Sun (1993), p. 359. -/
theorem newton_global_convergence {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (hα : β * (γ + δ) < 1)
    (hr0 : 0 ≤ r) (hr : β * ‖F x0‖ ≤ r * (1 - β * (γ + δ)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hx0 : x 0 = x0) (hrun : IsNewtonRun F x V) :
    (∀ k, x k ∈ Metric.closedBall x0 r) ∧ (∀ k, IsUnit (V k)) ∧
      ∃ xstar ∈ Metric.closedBall x0 r, F xstar = 0 ∧
        (∀ y ∈ Metric.closedBall x0 r, F y = 0 → y = xstar) ∧
        Tendsto x atTop (𝓝 xstar) ∧
        ∀ k, ‖x (k + 1) - xstar‖ ≤
          (β * (γ + δ)) / (1 - β * (γ + δ)) * ‖x (k + 1) - x k‖ := by sorry

end NonsmoothNewton.Global
