-- Prove2me | Theorems.Thm_HeldWolfeCrowder_Assignment_optSet_dimension
-- name    : HeldWolfeCrowder.Assignment.optSet_dimension
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:54:37.332926+00:00
-- url     : https://prove2.me/theorems/a2b45994-c0fe-44c1-82ea-7c6277cc1cbc
-- title:
--   Theorem 3.1 — a unique optimal assignment makes the dual optimal set n-dimensional
-- statement:
--   Let $A=(a_{ir})$ be a real $n\times n$ matrix, $a_{ir}$ the cost for which man $i$ does job $r$, and consider the assignment problem (3.1) of finding a one-to-one assignment $\sigma$ of men to jobs (job $r$ to man $\sigma(r)$) minimizing $\sum_r a_{\sigma(r)\,r}$. Its associated dual problem (3.3) is the maximization over $\pi\in\mathbb R^n$ of
--   $$w(\pi)=\sum_{i=1}^n\pi_i+\sum_{r=1}^n\min_s\,[a_{sr}-\pi_s].$$
--
--   **Theorem 3.1.** If the assignment problem has a unique optimal one-to-one assignment, then the optimal set $\Omega=\{\pi : w(\pi')\le w(\pi) \text{ for all } \pi'\in\mathbb R^n\}$ has dimension $n$:
--
--   $$\dim\operatorname{aff}\,\Omega = n .$$
--
--   The authors use this to explain why, on randomly generated assignment problems, the subgradient method usually stops at an iterate whose subgradient is exactly zero: a full-dimensional optimal set can be hit in finitely many steps.
--
--   **Formalization Note** The dimension of a convex set is that of its affine hull; in Lean it is `Module.finrank ℝ (vectorSpan ℝ Ω)`, the dimension of the direction of the affine span. Uniqueness is uniqueness among permutations (`∃! σ : Equiv.Perm (Fin n)`), not uniqueness of the linear-programming solution of (3.1). For $n=0$ the statement holds trivially.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 70, Theorem 3.1

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), p. 70, **Theorem 3.1**: if an assignment problem of order `n` has
a unique optimal one-to-one assignment, then the optimal set of its dual problem (3.3),
`max w`, has dimension `n` (the dimension of its affine hull). -/
theorem optSet_dimension {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (huniq : ∃! σ : Equiv.Perm (Fin n), IsOptimalAssignment a σ) :
    Module.finrank ℝ (vectorSpan ℝ (optSet a)) = n := by sorry

end HeldWolfeCrowder.Assignment
