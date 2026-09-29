-- Prove2me | Theorems.Thm_NonsmoothNewton_Global_root_unique_in_ball
-- name    : NonsmoothNewton.Global.root_unique_in_ball
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:10:37.235184+00:00
-- url     : https://prove2.me/theorems/d01301ce-8c74-40d4-88c4-01f9bd667379
-- title:
--   Theorem 3.3, proof — $F$ has at most one zero in $S$
-- statement:
--   Let $F : \mathbb{R}^n \to \mathbb{R}^n$ be locally Lipschitz, $S = \{x : \|x - x^0\| \le r\}$, and assume on $S$ (with constants $\beta, \gamma, \delta$):
--
--   1. $F$ is semismooth at every point of $S$;
--   2. for all $x \in S$, every $V \in \partial F(x)$ is nonsingular with $\|V^{-1}\| \le \beta$;
--   3. for all $x, y \in S$ and $V \in \partial F(x)$, $\|V(y-x) - F'(x;y-x)\| \le \gamma\|y - x\|$;
--   4. for all $x, y \in S$, $\|F(y) - F(x) - F'(x;y-x)\| \le \delta\|y - x\|$;
--   5. $\alpha = \beta(\gamma + \delta) < 1$.
--
--   If $x^*, y^* \in S$ and $F(x^*) = F(y^*) = 0$, then $y^* = x^*$. Indeed, for $V^* \in \partial F(x^*)$ the hypotheses give
--
--   $$
--   \|y^* - x^*\| \le \alpha\,\|y^* - x^*\| ,
--   $$
--
--   which forces $\|y^* - x^*\| = 0$ since $\alpha < 1$.
--
--   This is the uniqueness part of Theorem 3.3.
--
--   **Formalization Note** The existence of some $V^* \in \partial F(x^*)$ is not assumed; it is a consequence of local Lipschitzness (the generalized Jacobian of a locally Lipschitz map is nonempty).
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 360, Section 3, proof of Theorem 3.3, fifth to seventh displays

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Proof of Theorem 3.3 (Qi–Sun 1993, p. 360, lower half): under the hypotheses of
Theorem 3.3, `F` has at most one zero in `S`. -/
theorem root_unique_in_ball {n : ℕ}
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
    (xstar ystar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ Metric.closedBall x0 r) (hystar : ystar ∈ Metric.closedBall x0 r)
    (hFx : F xstar = 0) (hFy : F ystar = 0) :
    ystar = xstar := by sorry

end NonsmoothNewton.Global
