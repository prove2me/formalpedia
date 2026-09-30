-- Prove2me | Theorems.Thm_NonconvexSplitting_ADMMKL_augLag_semialgebraic
-- name    : NonconvexSplitting.ADMMKL.augLag_semialgebraic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T18:44:39.570914+00:00
-- url     : https://prove2.me/theorems/a5c77ac3-a012-4e02-8479-b13237de6a0a
-- title:
--   $L_\beta$ is semi-algebraic when $h$ and $P$ are
-- statement:
--   Let $h:\mathbb R^n\to\mathbb R$, $P:\mathbb R^m\to(-\infty,+\infty]$, $\mathcal M:\mathbb R^n\to\mathbb R^m$ linear and $\beta\in\mathbb R$. If $h$ and $P$ are semi-algebraic, then the augmented Lagrangian
--   $$
--   (x,y,z)\mapsto L_\beta(x,y,z)=h(x)+P(y)-\langle z,\mathcal Mx-y\rangle+\frac\beta2\|\mathcal Mx-y\|^2
--   $$
--   is a semi-algebraic function on $\mathbb R^{n+m+m}$.
--
--   Together with the fact that proper closed semi-algebraic functions are KL functions, this is how the semi-algebraic hypothesis of Theorem 3 enters the proof.
--
--   **Formalization Note** $\mathbb R^{n+m+m}$ is identified with $\mathbb R^n\times\mathbb R^m\times\mathbb R^m$ by splitting coordinates in the order $x,y,z$ (`xyzOfCoords`). Semi-algebraicity of the extended-valued $P$ and $L_\beta$ is that of the graph over their real values.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 14, "Next, notice that the function (x, y, z) ↦ Lβ(x, y, z) is semi-algebraic due to the semi-algebraicity of h and P"

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_IsProxADMMSeq
import Definitions.Def_NonconvexSplitting_ADMMKL_AugLagProd
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic
open NonconvexSplitting.Shared

open Filter Topology
open scoped InnerProductSpace

namespace NonconvexSplitting.ADMMKL

/-- Li–Pong (p. 14): if `h` and `P` are semi-algebraic then so is `(x, y, z) ↦ L_β(x, y, z)`,
read on `ℝ^{n+m+m}` through the coordinate identification `xyzOfCoords`. -/
theorem augLag_semialgebraic {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hh : IsSemialgebraicFn (fun u : EuclideanSpace ℝ (Fin n) => ((h u : ℝ) : EReal)))
    (hP : IsSemialgebraicFn P) :
    IsSemialgebraicFn (fun v : EuclideanSpace ℝ (Fin (n + m + m)) => augLagX h P M β (xyzOfCoords v)) := by sorry

end NonconvexSplitting.ADMMKL
