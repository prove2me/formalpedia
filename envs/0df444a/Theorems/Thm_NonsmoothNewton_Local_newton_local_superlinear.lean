-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_newton_local_superlinear
-- name    : NonsmoothNewton.Local.newton_local_superlinear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:05:30.986207+00:00
-- url     : https://prove2.me/theorems/f6ea5f6f-1904-4040-a874-eda2cb7a2f1d
-- title:
--   Theorem 3.2 — local superlinear convergence of the nonsmooth Newton method at a semismooth regular root
-- statement:
--   Let $F : \mathbb R^n \to \mathbb R^n$ be locally Lipschitz and let $x^*$ be a solution of $F(x) = 0$ (3.1). Suppose $F$ is semismooth at $x^*$ and every $V \in \partial F(x^*)$ is nonsingular. Consider the nonsmooth Newton method
--
--   $$
--   x^{k+1} = x^k - V_k^{-1} F(x^k), \qquad V_k \in \partial F(x^k). \tag{3.2}
--   $$
--
--   Then there is $\delta > 0$ such that:
--
--   1. every $V \in \partial F(y)$ with $\|y - x^*\| < \delta$ is nonsingular, and a Newton step from such a point $y$ (with any $V \in \partial F(y)$) lands at a point again within distance $\delta$ of $x^*$; so the iteration is well defined from every starting point in this neighbourhood;
--   2. every run $(x^k, V_k)$ of (3.2) with $\|x^0 - x^*\| < \delta$, for every choice of $V_k \in \partial F(x^k)$, has all $V_k$ nonsingular, converges to $x^*$, and converges superlinearly:
--   $$
--   \|x^{k+1} - x^*\| = o(\|x^k - x^*\|) \qquad (k \to \infty).
--   $$
--
--   This is the basic local convergence theorem for Newton's method with generalized Jacobians: it replaces the classical smoothness assumption by semismoothness and the nonsingular Jacobian by a nonsingular generalized Jacobian.
--
--   **Formalization Note** The printed theorem says the iteration "is well-defined and convergent to $x^*$ in a neighborhood of $x^*$"; the superlinear rate is the proof's display (3.3) and is stated here, as a little-$o$ along the sequence (`Asymptotics.IsLittleO` at infinity, no division by $\|x^k - x^*\|$). "Well defined" is stated as part 1 (nonsingularity in the neighbourhood and invariance of the neighbourhood under one step) and as nonsingularity of every $V_k$ of every run. A run is a sequence with $V_k \in \partial F(x^k)$ and $V_k(x^{k+1}-x^k) = -F(x^k)$; $\delta$ is chosen before the run. $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 359, Theorem 3.2 (first sentence) and proof, Eq. (3.3)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_NonsmoothNewton_Local_IsNewtonRun
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Theorem 3.2 (local convergence), p. 359, with the superlinear rate (3.3) of its
proof. Let `F : ℝⁿ → ℝⁿ` be locally Lipschitz, `F(x*) = 0`, `F` semismooth at `x*`, and every
`V ∈ ∂F(x*)` nonsingular. Then there is `δ > 0` such that
* every `V ∈ ∂F(y)` with `‖y - x*‖ < δ` is nonsingular, and a Newton step (3.2) from such a `y`
  lands again within `δ` of `x*` (the iteration is well defined in this neighbourhood);
* every run of (3.2) with `‖x⁰ - x*‖ < δ`, for every choice of `V_k ∈ ∂F(x^k)`, has all `V_k`
  nonsingular, converges to `x*`, and `‖x^{k+1} - x*‖ = o(‖x^k - x*‖)`. -/
theorem newton_local_superlinear {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : F xstar = 0) (hsemi : SemismoothAt F xstar)
    (hns : ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F xstar, IsUnit V) :
    ∃ δ > 0,
      (∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ < δ → ∀ W ∈ NonsmoothNewton.Shared.clarkeJac F y, IsUnit W) ∧
      (∀ y y' : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ < δ → ∀ W ∈ NonsmoothNewton.Shared.clarkeJac F y,
        W (y' - y) = - F y → ‖y' - xstar‖ < δ) ∧
      (∀ (x : ℕ → EuclideanSpace ℝ (Fin n))
        (V : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ‖x 0 - xstar‖ < δ → IsNewtonRun F x V →
          (∀ k, IsUnit (V k)) ∧ Tendsto x atTop (𝓝 xstar) ∧
          (fun k => x (k + 1) - xstar) =o[atTop] (fun k => x k - xstar)) := by sorry

end NonsmoothNewton.Local
