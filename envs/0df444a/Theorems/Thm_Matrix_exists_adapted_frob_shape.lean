-- Prove2me | Theorems.Thm_Matrix_exists_adapted_frob_shape
-- name    : Matrix.exists_adapted_frob_shape
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/990eb20a-d8ba-55c9-a8b7-9b402605af10
-- title:
--   Shape of Frobenius in a basis adapted to a nilpotent line
-- statement:
--   Let $R$ be a commutative ring that is a domain, and let $N_0$, $P$, $F$ be $2\times 2$ matrices over $R$. Assume the determinant of $P$ is a unit in $R$, let $t \in R$ be nonzero, and assume that $P$ conjugates $N_0$ to the elementary nilpotent matrix with the single nonzero entry $t$ in position $(0,1)$, in the form $N_0 \cdot P = P \cdot \begin{pmatrix} 0 & t \\ 0 & 0\end{pmatrix}$. Assume further that for some scalar $q \in R$ one has the commutation relation $F \cdot N_0 = q \cdot (N_0 \cdot F)$, where $q \cdot {}$ denotes entrywise scalar multiplication. Then there exists a $2\times 2$ matrix $F'$ over $R$ such that $F \cdot P = P \cdot F'$, the entry $F'_{1,0}$ vanishes, and $F'_{0,0} = q\, F'_{1,1}$. Thus in the coordinates given by $P$ the matrix $F$ becomes upper triangular with its two diagonal entries in the ratio $q$.
--
--   This is the elementary matrix input for the statement that, in a basis adapted to the nilpotent line cut out by tame inertia, a Frobenius element satisfying $F N_0 = q\,(N_0 F)$ is upper triangular with diagonal eigenvalue ratio $q$. It is used by [`GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt`](thm.html#GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_adapted_frob_shape.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.exists_adapted_frob_shape
    {R : Type} [CommRing R] [IsDomain R]
    (N₀ P F : Matrix (Fin 2) (Fin 2) R) (hP : IsUnit P.det)
    (t : R) (ht : t ≠ 0) (hN₀P : N₀ * P = P * Matrix.of ![![0, t], ![0, 0]])
    (q : R) (hFN : F * N₀ = q • (N₀ * F)) :
    ∃ F' : Matrix (Fin 2) (Fin 2) R,
      F * P = P * F' ∧ F' 1 0 = 0 ∧ F' 0 0 = q * F' 1 1 := by sorry
