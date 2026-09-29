-- Prove2me | Theorems.Thm_KannanLattice_Core_exists_basis_mem_of_primitive
-- name    : KannanLattice.Core.exists_basis_mem_of_primitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:12:46.785029+00:00
-- url     : https://prove2.me/theorems/cb47fc83-8542-47fc-94be-5705c0872977
-- title:
--   Proposition 1.9 — a primitive lattice vector belongs to some basis
-- statement:
--   Let $b_1,\dots,b_m$ be linearly independent vectors of $\mathcal R^k$ and $L=L(b_1,\dots,b_m)$. Let $v\in L$ be nonzero and **primitive**: $\lambda v\notin L$ for every real $\lambda\in(0,1)$. Then there is a basis of $L$ containing $v$, that is, linearly independent vectors $b_1',\dots,b_m'$ with
--
--   $$L(b_1',\dots,b_m')=L(b_1,\dots,b_m)\quad\text{and}\quad v\in\{b_1',\dots,b_m'\}.$$
--
--   Primitive vectors are exactly the vectors that can start a basis; in particular a shortest nonzero vector of a lattice can be completed to a basis, which is how reduced bases are built.
--
--   **Formalization Note** "A basis of the lattice" is a linearly independent family of the same size $m$ generating the same lattice over $\mathbb Z$ (every basis of an $m$-dimensional lattice has $m$ elements, Lemma (1.1)).
-- source:
--   Kannan, Minkowski's Convex Body Theorem and Integer Programming, Math. Oper. Res. 12 (1987); author's final manuscript (CMU-CS-96-105), p. 8, Proposition 1.9

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- Proposition 1.9 of Kannan (1987), p. 8: a primitive vector `v` of the lattice `L(b)` (nonzero,
and `t • v ∉ L(b)` for every real `t ∈ (0, 1)`) belongs to some basis of the lattice. -/
theorem exists_basis_mem_of_primitive (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (v : EuclideanSpace ℝ (Fin k)) (hv : v ∈ lattice b) (hv0 : v ≠ 0)
    (hprim : ∀ t : ℝ, 0 < t → t < 1 → t • v ∉ lattice b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ v ∈ Set.range b' := by sorry

end KannanLattice.Core
