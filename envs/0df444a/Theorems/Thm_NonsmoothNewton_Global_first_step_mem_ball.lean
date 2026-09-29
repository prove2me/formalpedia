-- Prove2me | Theorems.Thm_NonsmoothNewton_Global_first_step_mem_ball
-- name    : NonsmoothNewton.Global.first_step_mem_ball
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:08:14.819712+00:00
-- url     : https://prove2.me/theorems/10bb4993-e600-4fb9-a4de-441c826dd3cd
-- title:
--   Theorem 3.3, proof — the first Newton step satisfies $\|x^1-x^0\|\le\beta\|F(x^0)\|\le r(1-\alpha)$, so $x^1\in S$
-- statement:
--   Let $F : \mathbb{R}^n \to \mathbb{R}^n$ be locally Lipschitz, let $x^0 \in \mathbb{R}^n$, $r \ge 0$, and let $S = \{x : \|x - x^0\| \le r\}$ (Euclidean norm). Assume the hypotheses of Theorem 3.3 on $S$ with constants $\beta, \gamma, \delta$:
--
--   1. $F$ is semismooth at every point of $S$;
--   2. for all $x \in S$, every $V \in \partial F(x)$ is nonsingular with $\|V^{-1}\| \le \beta$;
--   3. for all $x, y \in S$ and $V \in \partial F(x)$, $\|V(y-x) - F'(x;y-x)\| \le \gamma\|y - x\|$;
--   4. for all $x, y \in S$, $\|F(y) - F(x) - F'(x;y-x)\| \le \delta\|y - x\|$;
--   5. $\alpha = \beta(\gamma+\delta) < 1$ and $\beta\|F(x^0)\| \le r(1-\alpha)$.
--
--   If $V_0 \in \partial F(x^0)$ and $x^1$ satisfies $V_0(x^1 - x^0) = -F(x^0)$, then
--
--   $$
--   \|x^1 - x^0\| \le \beta\|F(x^0)\| \le r(1-\alpha), \qquad\text{so } x^1 \in S.
--   $$
--
--   This is the base case of the argument that all Newton iterates stay in the ball $S$.
--
--   **Formalization Note** $F'(x;h)$ is `dirDeriv`, meaningful here because $F$ is semismooth on $S$. Nonsingularity with $\|V^{-1}\|\le\beta$ is the existence of a two-sided inverse $W$ with operator norm at most $\beta$. The radius condition $r \ge 0$ is made explicit (the paper's $S$ is a ball around $x^0$).
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 360, Section 3, proof of Theorem 3.3, first display

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Proof of Theorem 3.3 (Qi–Sun 1993, p. 360, first display): the first Newton step from `x0`
has length at most `β ‖F x0‖ ≤ r (1 - α)`, so `x1 ∈ S`. -/
theorem first_step_mem_ball {n : ℕ}
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
    (V0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (x1 : EuclideanSpace ℝ (Fin n))
    (hV0 : V0 ∈ clarkeJac F x0) (hstep : V0 (x1 - x0) = -F x0) :
    ‖x1 - x0‖ ≤ β * ‖F x0‖ ∧ ‖x1 - x0‖ ≤ r * (1 - β * (γ + δ)) ∧ x1 ∈ Metric.closedBall x0 r := by sorry

end NonsmoothNewton.Global
