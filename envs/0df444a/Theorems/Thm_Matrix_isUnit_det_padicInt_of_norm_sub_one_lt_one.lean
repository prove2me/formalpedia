-- Prove2me | Theorems.Thm_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one
-- name    : Matrix.isUnit_det_padicInt_of_norm_sub_one_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/4c8d52ce-a984-54e2-b7ca-f039f20dd068
-- title:
--   Matrices congruent to the identity over ℤₚ have unit determinant
-- statement:
--   For a prime $p$, a natural number $n$ and a matrix $P \in M_n(\mathbb{Z}_p)$ indexed by `Fin n`, suppose that for all indices $i, j$ the $p$-adic norm $\|P_{ij} - \delta_{ij}\|$ is strictly less than $1$, where $\delta_{ij}$ denotes the $(i,j)$ entry of the identity matrix of $M_n(\mathbb{Z}_p)$; that is, every entry of $P$ differs from the corresponding entry of the identity matrix by an element of the maximal ideal $p\mathbb{Z}_p$. The conclusion is that $\det P$ is a unit of the ring $\mathbb{Z}_p$. Note that $n$ is arbitrary, including $n = 0$, where the determinant is $1$.
--
--   This is the standard fact that $1 + pM_n(\mathbb{Z}_p) \subseteq \mathrm{GL}_n(\mathbb{Z}_p)$, phrased via the $p$-adic norm on entries. It supplies the invertibility hypothesis needed by [`Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det`](thm.html#Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.isUnit_det_padicInt_of_norm_sub_one_lt_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Matrix (Fin n) (Fin n) ℤ_[p])
    (h : ∀ i j, ‖P i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) :
    IsUnit P.det := by sorry
