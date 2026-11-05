-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_abs_le_of_mem_dualFeasible_sublevel
-- name    : ModernConvex.Relaxations.abs_le_of_mem_dualFeasible_sublevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:34:52.946195+00:00
-- url     : https://prove2.me/theorems/e160eb23-83d5-40d6-a2b7-c030e9e42cfa
-- title:
--   The Max-Cut SDP dual is bounded on a sublevel set
-- statement:
--   **The feasible set of the Max-Cut SDP dual is bounded on a sublevel set.**
--
--   The dual of the Max-Cut semidefinite relaxation is $\min\{\tfrac14(\sum_{i,j}a_{ij}+\sum_i\lambda_i) : a+\operatorname{diag}\lambda\succeq0\}$. Its feasible set is unbounded — increasing any $\lambda_i$ preserves feasibility — but a minimizer never leaves a sublevel set, and sublevel sets are bounded: for dual feasible $\lambda$ and any $i$,
--   $$-a_{ii}\;\le\;\lambda_i\;\le\;U+\sum_{j\ne i}a_{jj}\qquad\text{whenever}\quad \sum_j\lambda_j\le U .$$
--
--   The lower bound is immediate: the diagonal entries of a positive semidefinite matrix are nonnegative, so $0\le(a+\operatorname{diag}\lambda)_{ii}=a_{ii}+\lambda_i$. The upper bound follows by summing the lower bounds over $j\ne i$ and using $\sum_j\lambda_j\le U$:
--   $$\lambda_i=\sum_j\lambda_j-\sum_{j\ne i}\lambda_j\le U+\sum_{j\ne i}a_{jj}.$$
--
--   Hence the sublevel set lies in the box $\prod_i[-a_{ii},\,U+\sum_{j\ne i}a_{jj}]$, which is compact. This supplies the "bounded convex body" hypothesis of the ellipsoid method as stated in Bubeck's Theorem 2.4, for a run on the dual spectrahedron.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; the boundedness hypothesis of Bubeck, arXiv:1405.4980v2, Thm 2.4, p. 250.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **The sublevel set of the Max-Cut SDP dual is bounded.** Every dual feasible `λ` with
`Σ_i λ_i ≤ U` satisfies `-a_ii ≤ λ_i ≤ U + Σ_{j≠i} a_jj`, because the diagonal of a positive
semidefinite matrix is nonnegative. -/
theorem abs_le_of_mem_dualFeasible_sublevel {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ}
    {lam : Fin n → ℝ} (h : (a + Matrix.diagonal lam).PosSemidef) {U : ℝ}
    (hlev : ∑ j, lam j ≤ U) (i : Fin n) :
    lam i ∈ Set.Icc (-(a i i)) (U + ∑ j ∈ Finset.univ.erase i, a j j) := by sorry

end ModernConvex.Relaxations
