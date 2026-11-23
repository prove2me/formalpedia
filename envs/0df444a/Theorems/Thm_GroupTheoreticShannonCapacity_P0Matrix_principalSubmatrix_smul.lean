-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_smul
-- name    : GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:26.147538+00:00
-- url     : https://prove2.me/theorems/9f6d7c7a-1342-4759-ac41-75ec8d1ac0a1
-- title:
--   P0 Matrix: principal Submatrix smul
-- statement:
--   Principal submatrix commutes with scalar multiplication
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L672-L677
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L672-L677

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_smul (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (S : Finset (Fin n)) :
    principalSubmatrix n (c • M) S = c • principalSubmatrix n M S := by sorry
