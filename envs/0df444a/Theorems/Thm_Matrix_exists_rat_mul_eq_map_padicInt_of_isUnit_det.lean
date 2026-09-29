-- Prove2me | Theorems.Thm_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det
-- name    : Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/55b137cf-bfc0-5830-867b-fd5065042082
-- title:
--   Factorisation GLₙ(ℚₚ)=GLₙ(ℤₚ)cdotGLₙ(ℚ)
-- statement:
--   Let $p$ be a prime and $n$ a natural number, and let $M$ be an $n \times n$ matrix with entries in $\mathbb{Q}_p$ whose determinant is a unit of $\mathbb{Q}_p$, i.e. $M \in \mathrm{GL}_n(\mathbb{Q}_p)$. The assertion is that there exist an $n \times n$ matrix $Q$ with entries in $\mathbb{Q}$ and an $n \times n$ matrix $P$ with entries in $\mathbb{Z}_p$ such that $\det Q$ is a unit of $\mathbb{Q}$ (equivalently $\det Q \neq 0$), $\det P$ is a unit of $\mathbb{Z}_p$ (equivalently $\|\det P\| = 1$), and, after transporting $Q$ entrywise into $\mathbb{Q}_p$ along the structure map $\mathbb{Q} \to \mathbb{Q}_p$ and $P$ entrywise along the inclusion $\mathbb{Z}_p \to \mathbb{Q}_p$, one has the identity of matrices over $\mathbb{Q}_p$
--   $$M \cdot Q = P .$$
--   Thus every element of $\mathrm{GL}_n(\mathbb{Q}_p)$ can be written as an element of $\mathrm{GL}_n(\mathbb{Z}_p)$ times the inverse of the image of an element of $\mathrm{GL}_n(\mathbb{Q})$.
--
--   This is the matrix form of the statement that a $\mathbb{Z}_p$-lattice in $\mathbb{Q}_p^n$ admits a basis consisting of vectors with rational coordinates, i.e. the local factorisation $\mathrm{GL}_n(\mathbb{Q}_p) = \mathrm{GL}_n(\mathbb{Z}_p)\cdot\mathrm{GL}_n(\mathbb{Q})$. It is used in coordinate-free form by [`Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange`](thm.html#Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ_[p]) (hM : IsUnit M.det) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℚ) (P : Matrix (Fin n) (Fin n) ℤ_[p]),
      IsUnit Q.det ∧ IsUnit P.det ∧
      M * Q.map (algebraMap ℚ ℚ_[p]) = P.map (algebraMap ℤ_[p] ℚ_[p]) := by sorry
