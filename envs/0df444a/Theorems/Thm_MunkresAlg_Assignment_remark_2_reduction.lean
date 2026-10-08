-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_remark_2_reduction
-- name    : MunkresAlg.Assignment.remark_2_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:53:39.299223+00:00
-- url     : https://prove2.me/theorems/dd9c1e53-17fe-479f-b5b2-e97439eae8bc
-- title:
--   §1, Remark (2), p. 33 — replacing x_ij by x_ij − u_i − v_j does not change the optimal assignments
-- statement:
--   Let $A=(x_{ij})$ be a real $n\times n$ matrix and let $u_1,\dots,u_n$ and $v_1,\dots,v_n$ be arbitrary real constants. Put $y_{ij}=x_{ij}-u_i-v_j$. For an assignment given by a permutation $\sigma$ of $\{1,\dots,n\}$, where $\sigma(r)$ is the row assigned to column $r$, write $c_A(\sigma)=\sum_r x_{\sigma(r) r}$. Then for every permutation $\sigma$,
--   $$
--   \sigma \text{ minimizes } c_{(x_{ij})} \iff \sigma \text{ minimizes } c_{(y_{ij})}.
--   $$
--   That is, the solution of the assignment problem is not changed by subtracting constants from rows and columns.
--
--   This is the reason every matrix transformation of the algorithm (row and column reductions, and Step 3) preserves the solution: the final starred zeros are optimal for the original matrix.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 33, §1, Remark (2)

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace MunkresAlg.Assignment

/-- Munkres (1957), §1, Remark (2), p. 33: subtracting arbitrary row constants `u i` and column
constants `v j` from the matrix does not change the set of optimal assignments. -/
theorem remark_2_reduction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ ↔
      HeldWolfeCrowder.Assignment.IsOptimalAssignment (fun i j => A i j - u i - v j) σ := by sorry

end MunkresAlg.Assignment
