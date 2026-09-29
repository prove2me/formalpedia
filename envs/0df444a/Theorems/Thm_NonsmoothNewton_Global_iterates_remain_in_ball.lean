-- Prove2me | Theorems.Thm_NonsmoothNewton_Global_iterates_remain_in_ball
-- name    : NonsmoothNewton.Global.iterates_remain_in_ball
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-27T00:09:11.152889+00:00
-- url     : https://prove2.me/theorems/cd9f7230-f3c5-4d4c-926a-9b553b519de6
-- title:
--   Theorem 3.3, proof — the iterates remain in $S$ and $\|x^{k+1}-x^k\|\le r\alpha^k(1-\alpha)$
-- statement:
--   Let $F : \mathbb{R}^n \to \mathbb{R}^n$ be locally Lipschitz, $x^0 \in \mathbb{R}^n$, $r \ge 0$, $S = \{x : \|x - x^0\| \le r\}$, and assume the hypotheses of Theorem 3.3:
--
--   1. $F$ is semismooth at every point of $S$;
--   2. for all $x \in S$, every $V \in \partial F(x)$ is nonsingular with $\|V^{-1}\| \le \beta$;
--   3. for all $x, y \in S$ and $V \in \partial F(x)$, $\|V(y-x) - F'(x;y-x)\| \le \gamma\|y - x\|$;
--   4. for all $x, y \in S$, $\|F(y) - F(x) - F'(x;y-x)\| \le \delta\|y - x\|$;
--   5. $\alpha = \beta(\gamma+\delta) < 1$ and $\beta\|F(x^0)\| \le r(1-\alpha)$.
--
--   Then every run $(x^k, V_k)_{k \ge 0}$ of the nonsmooth Newton iteration (3.2) started at $x^0$ (any choice $V_k \in \partial F(x^k)$) satisfies, for all $k \ge 0$,
--
--   $$
--   x^k \in S \qquad\text{and}\qquad \|x^{k+1} - x^k\| \le r\,\alpha^k(1-\alpha).
--   $$
--
--   The geometric bound on the steps is what makes the iterates a Cauchy sequence in $S$.
--
--   **Formalization Note** $r \ge 0$ is explicit. $F'(x;h)$ is `dirDeriv`; $\|V^{-1}\|\le\beta$ is the existence of a two-sided inverse of operator norm at most $\beta$.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 360, Section 3, proof of Theorem 3.3, second and third displays

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Proof of Theorem 3.3 (Qi–Sun 1993, p. 360, second and third displays): every run of (3.2)
from `x0` has steps `‖x^{k+1} - x^k‖ ≤ r α^k (1 - α)` and stays in `S`. -/
theorem iterates_remain_in_ball {n : ℕ}
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
    ∀ k, x k ∈ Metric.closedBall x0 r ∧
      ‖x (k + 1) - x k‖ ≤ r * (β * (γ + δ)) ^ k * (1 - β * (γ + δ)) := by sorry

end NonsmoothNewton.Global
