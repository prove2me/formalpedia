-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_diagonal_mul
-- name    : GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_diagonal_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:26.964395+00:00
-- url     : https://prove2.me/theorems/54f441e0-1ae7-493c-b755-0863eb6c4f31
-- title:
--   P0 Matrix: principal Submatrix diagonal mul
-- statement:
--   Principal submatrix of left diagonal multiplication
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L690-L701
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L690-L701

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_diagonal_mul (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (S : Finset (Fin n)) :
    principalSubmatrix n (diagonal d * M) S =
    diagonal (d ∘ S.orderEmbOfFin rfl) * principalSubmatrix n M S := by sorry
