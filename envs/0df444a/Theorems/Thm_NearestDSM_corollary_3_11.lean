-- Prove2me | Theorems.Thm_NearestDSM_corollary_3_11
-- name    : NearestDSM.corollary_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:45.173477+00:00
-- url     : https://prove2.me/theorems/6851628e-d30d-4168-8864-72a68e901c60
-- title:
--   Corollary 3.11 — at a vertex, $\partial F$ contains a nonsingular matrix
-- statement:
--   If $y$ is a vertex of the polyhedron $[\tilde y]$, then $\partial F(y)$ contains at least one nonsingular matrix. In particular, the maximal matrix
--   $$
--   V=A\,\mathrm{Diag}(\mathrm{vec}(M))A^T,\qquad M\ \text{maximal for }y,
--   $$
--   is nonsingular.
--
--   This is why the Newton step of Algorithm 3.1, taken at a vertex with the maximal $V$, is well defined.
--
--   **Formalization Note** $\partial F(y)$ is the set (2.7).
--
--   Differences from the source:
--   - encoding: Clarke's generalized Jacobian $\partial F(y)$ → the set (2.7) $\{V(M): M\in\mathcal M(y)\}$; reason: the paper's own formula for $\partial F(y)$ (p.8)
--   - encoding: size $n\ge1$ → `n + 1`; nonsingular → $\det\ne0$; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Corollary 3.11, p.18

import Mathlib
import Definitions.Def_NearestDSM_equivClass
import Definitions.Def_NearestDSM_IsMaximalM
import Definitions.Def_NearestDSM_jacSet

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Corollary 3.11, p.18. If `y` is a vertex of the polyhedron `[ỹ]`, then
`∂F(y)` contains at least one nonsingular matrix. In particular, the maximal matrix `V ∈ ∂F(y)` is
nonsingular.

**Formalization Note.** `∂F(y)` is encoded by (2.7) (`jacSet`); the maximal `V ∈ ∂F(y)` is
`V(M)` for `M` maximal for `y` (3.9), p.17. "Nonsingular" is `det ≠ 0`. The paper's size `n` is
`n + 1`. -/
theorem corollary_3_11 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (yt y : Dual n)
    (hy : y ∈ Set.extremePoints ℝ (equivClass Xh yt)) :
    (∃ V ∈ jacSet Xh y, V.det ≠ 0) ∧
      ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, IsMaximalM Xh y M → (Vmat M).det ≠ 0 := by sorry

end NearestDSM
