-- Prove2me | Theorems.Thm_Matrix_exists_adapted_basis_of_unipotent_family
-- name    : Matrix.exists_adapted_basis_of_unipotent_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/ef9aac5b-b7e6-5270-800d-0df45eb31c03
-- title:
--   Adapted basis for a unipotent family of 2× 2 matrices
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and a valuation ring, and let $T$ be a set of $2\times 2$ matrices over $R$ (indexed by `Fin 2`) subject to two conditions: $T$ is closed under multiplication, i.e. $AB \in T$ whenever $A, B \in T$; and every $A \in T$ satisfies $(A-1)^2 = 0$, where $1$ is the identity matrix. Suppose further that $T$ contains a matrix $A_0$ with $A_0 \neq 1$. Then there is a single $2 \times 2$ matrix $P$ over $R$ whose determinant is a unit of $R$, such that: first, there exists $t \in R$ with $t \neq 0$ and $A_0 P = P \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$; and second, for every $A \in T$ there exists $s \in R$ with $A P = P \begin{pmatrix} 1 & s \\ 0 & 1\end{pmatrix}$. Since $\det P$ is a unit, this says that conjugation by $P$ carries every member of $T$ simultaneously into the group of upper triangular unipotent matrices, with the parameter attached to $A_0$ nonzero. Note that $T$ is not assumed to contain the identity or to be closed under inverses.
--
--   This is an integral form, over a valuation ring, of Kolchin's simultaneous triangularisation statement for unipotent families, in the case of $2\times 2$ matrices: the conjugating matrix is required to be invertible over $R$ itself, not merely over the fraction field. It is used in bounding the length of a level quotient of a deformation ring for representations that are unipotent on inertia, via [`GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt`](thm.html#GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_adapted_basis_of_unipotent_family.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Valuation.ValuationRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.exists_adapted_basis_of_unipotent_family
    {R : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] (T : Set (Matrix (Fin 2) (Fin 2) R))
    (hmul : ∀ A ∈ T, ∀ B ∈ T, A * B ∈ T)
    (hsq : ∀ A ∈ T, (A - 1) * (A - 1) = 0)
    (A₀ : Matrix (Fin 2) (Fin 2) R) (hA₀ : A₀ ∈ T) (hA₀ne : A₀ ≠ 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧
      (∃ t : R, t ≠ 0 ∧ A₀ * P = P * Matrix.of ![![1, t], ![0, 1]]) ∧
      ∀ A ∈ T, ∃ s : R, A * P = P * Matrix.of ![![1, s], ![0, 1]] := by sorry
