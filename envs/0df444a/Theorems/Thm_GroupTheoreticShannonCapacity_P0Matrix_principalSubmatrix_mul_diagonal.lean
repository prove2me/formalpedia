-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_mul_diagonal
-- name    : GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_mul_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:35.184885+00:00
-- url     : https://prove2.me/theorems/3a83da86-7e06-4709-9653-e0d59b4282cf
-- title:
--   P0 Matrix: principal Submatrix mul diagonal
-- statement:
--   Principal submatrix of right diagonal multiplication
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L704-L715
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L704-L715

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_mul_diagonal (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (S : Finset (Fin n)) :
    principalSubmatrix n (M * diagonal d) S =
    principalSubmatrix n M S * diagonal (d ∘ S.orderEmbOfFin rfl) := by sorry
