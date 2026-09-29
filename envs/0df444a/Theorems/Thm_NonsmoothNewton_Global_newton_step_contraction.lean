-- Prove2me | Theorems.Thm_NonsmoothNewton_Global_newton_step_contraction
-- name    : NonsmoothNewton.Global.newton_step_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:08:39.940552+00:00
-- url     : https://prove2.me/theorems/b9b589c4-35af-4643-aa36-f158f6a884f3
-- title:
--   Theorem 3.3, proof — one-step contraction $\|x^{k+1}-x^k\|\le\beta(\delta+\gamma)\|x^k-x^{k-1}\|$
-- statement:
--   Let $F : \mathbb{R}^n \to \mathbb{R}^n$ be locally Lipschitz, $S = \{x : \|x - x^0\| \le r\}$, and assume on $S$ (with constants $\beta, \gamma, \delta$):
--
--   1. $F$ is semismooth at every point of $S$;
--   2. for all $x \in S$, every $V \in \partial F(x)$ is nonsingular with $\|V^{-1}\| \le \beta$;
--   3. for all $x, y \in S$ and $V \in \partial F(x)$, $\|V(y-x) - F'(x;y-x)\| \le \gamma\|y - x\|$;
--   4. for all $x, y \in S$, $\|F(y) - F(x) - F'(x;y-x)\| \le \delta\|y - x\|$.
--
--   Let $x^{k-1}, x^k \in S$ and $x^{k+1} \in \mathbb{R}^n$ be three consecutive Newton points: $V_{k-1} \in \partial F(x^{k-1})$ with $V_{k-1}(x^k - x^{k-1}) = -F(x^{k-1})$, and $V_k \in \partial F(x^k)$ with $V_k(x^{k+1} - x^k) = -F(x^k)$. Then
--
--   $$
--   \|x^{k+1} - x^k\| \le \beta\|F(x^k)\| \qquad\text{and}\qquad \|x^{k+1} - x^k\| \le \beta(\delta+\gamma)\,\|x^k - x^{k-1}\|.
--   $$
--
--   With $\alpha = \beta(\gamma+\delta) < 1$ this is the contraction that drives the whole global convergence proof.
--
--   **Formalization Note** Stated for arbitrary points rather than for a run, so it applies at every step $k \ge 1$. The hypotheses $\alpha < 1$ and $\beta\|F(x^0)\|\le r(1-\alpha)$ are not needed here and are omitted.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 360, Section 3, proof of Theorem 3.3, second display

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Proof of Theorem 3.3 (Qi–Sun 1993, p. 360, second display): two consecutive Newton steps
taken from points of `S` contract by the factor `α = β (γ + δ)`. -/
theorem newton_step_contraction {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (xkm1 xk xkp1 : EuclideanSpace ℝ (Fin n)) (Vkm1 Vk : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hxkm1 : xkm1 ∈ Metric.closedBall x0 r) (hxk : xk ∈ Metric.closedBall x0 r)
    (hVkm1 : Vkm1 ∈ clarkeJac F xkm1) (hstepkm1 : Vkm1 (xk - xkm1) = -F xkm1)
    (hVk : Vk ∈ clarkeJac F xk) (hstepk : Vk (xkp1 - xk) = -F xk) :
    ‖xkp1 - xk‖ ≤ β * ‖F xk‖ ∧
      ‖xkp1 - xk‖ ≤ β * (δ + γ) * ‖xk - xkm1‖ := by sorry

end NonsmoothNewton.Global
