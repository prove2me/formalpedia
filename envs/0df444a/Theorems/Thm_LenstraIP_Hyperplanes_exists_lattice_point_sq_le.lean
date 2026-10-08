-- Prove2me | Theorems.Thm_LenstraIP_Hyperplanes_exists_lattice_point_sq_le
-- name    : LenstraIP.Hyperplanes.exists_lattice_point_sq_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:13.970412+00:00
-- url     : https://prove2.me/theorems/98f4acfc-f7a0-488c-99f3-f3cc6a9b5e4c
-- title:
--   §1, p. 540, LEMMA (8) — every x ∈ ℝⁿ has a lattice point y with |x − y|² ≤ ¼(|b₁|² + ⋯ + |bₙ|²)
-- statement:
--   Let $b_1, \dots, b_n$ be any basis of $\mathbb R^n$ and $L = \sum_i \mathbb Z b_i$ the lattice it generates. Then every point of $\mathbb R^n$ lies within a controlled distance of $L$:
--   $$\forall x \in \mathbb R^n\ \exists y \in L:\quad |x - y|^2 \le \tfrac14\big(|b_1|^2 + \cdots + |b_n|^2\big).$$
--
--   This is the LEMMA of §1 of Lenstra's paper, equation (8). It is the covering estimate that, once the basis vectors are numbered by length, gives (10) and then the radius bound used in the goal theorem. The published theorem `KannanLattice.Core.exists_lattice_point_near_projection` (Kannan 1987, Proposition 4.2) proves the stronger form with the Gram–Schmidt lengths $|b_i^*| \le |b_i|$ in place of $|b_i|$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $L$ is `KannanLattice.Core.lattice b`, and "$b$ is a basis for $L$" is the hypothesis that the $n$ vectors $b_i$ are linearly independent over $\mathbb R$ (so they form a basis of $\mathbb R^n$ and $L$ is exactly their $\mathbb Z$-span). The statement covers every $n \ge 0$.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, p. 540, LEMMA (8)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

open KannanLattice.Core

namespace LenstraIP.Hyperplanes

/-- Lenstra (1983), §1, p. 540, LEMMA (8): for any basis `b₁, …, bₙ` of the lattice
`L = Σ ℤ bᵢ`, every `x ∈ ℝⁿ` has a lattice point `y` with `|x − y|² ≤ ¼(|b₁|² + ⋯ + |bₙ|²)`. -/
theorem exists_lattice_point_sq_le (n : ℕ) (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ lattice b, ‖x - y‖ ^ 2 ≤ (1 / 4 : ℝ) * ∑ i, ‖b i‖ ^ 2 := by sorry

end LenstraIP.Hyperplanes
