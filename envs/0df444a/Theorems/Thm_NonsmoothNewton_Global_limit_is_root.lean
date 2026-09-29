-- Prove2me | Theorems.Thm_NonsmoothNewton_Global_limit_is_root
-- name    : NonsmoothNewton.Global.limit_is_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:09:42.436316+00:00
-- url     : https://prove2.me/theorems/91c7db49-9daa-4bf2-804b-674403114a86
-- title:
--   Theorem 3.3, proof — a convergent run in $S$ has bounded $\|V_k\|$ and converges to a zero of $F$
-- statement:
--   Let $F : \mathbb{R}^n \to \mathbb{R}^n$ be locally Lipschitz and $S = \{x : \|x - x^0\| \le r\}$ a closed Euclidean ball. Let $(x^k, V_k)_{k\ge 0}$ be a run of the nonsmooth Newton iteration (3.2), i.e. $V_k \in \partial F(x^k)$ and $V_k(x^{k+1} - x^k) = -F(x^k)$ for all $k$, such that $x^k \in S$ for every $k$ and $x^k \to x^*$. Then:
--
--   1. the generalized Jacobians are uniformly bounded: there is $C$ with $\|V_k\| \le C$ for all $k$;
--   2. $x^* \in S$;
--   3. $x^*$ is a zero of $F$:
--
--   $$
--   \|F(x^*)\| = \lim_{k\to\infty}\|F(x^k)\| \le \lim_{k\to\infty}\|V_k\|\,\|x^{k+1} - x^k\| = 0 .
--   $$
--
--   This is the step of Theorem 3.3 that identifies the limit of the Newton iterates as a solution of $F(x) = 0$.
--
--   **Formalization Note** The uniform bound on $\|V_k\|$ is a conclusion, derived from local Lipschitzness of $F$ (the generalized Jacobian is bounded near a compact set); it is not assumed. $\|V_k\|$ is the operator norm.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 360, Section 3, proof of Theorem 3.3, fourth display

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Proof of Theorem 3.3 (Qi–Sun 1993, p. 360, middle): along a run of (3.2) that stays in the
closed ball `S` and converges to `xstar`, the generalized Jacobians `V k` are uniformly bounded,
`xstar ∈ S`, and `F xstar = 0`. -/
theorem limit_is_root {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hF : LocallyLipschitz F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hrun : IsNewtonRun F x V) (hS : ∀ k, x k ∈ Metric.closedBall x0 r)
    (xstar : EuclideanSpace ℝ (Fin n)) (hlim : Tendsto x atTop (𝓝 xstar)) :
    (∃ C : ℝ, ∀ k, ‖V k‖ ≤ C) ∧ xstar ∈ Metric.closedBall x0 r ∧ F xstar = 0 := by sorry

end NonsmoothNewton.Global
