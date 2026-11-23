-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_continuous_principalSubmatrix_det
-- name    : GroupTheoreticShannonCapacity.P0Matrix.continuous_principalSubmatrix_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:36.842132+00:00
-- url     : https://prove2.me/theorems/bfac6489-9a41-47b8-bebd-1d3c89d5587c
-- title:
--   P0 Matrix: continuous principal Submatrix det
-- statement:
--   The map sending a matrix to the determinant of a principal submatrix is continuous
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L752-L754
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L752-L754

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.continuous_principalSubmatrix_det (n : ℕ) (S : Finset (Fin n)) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => (principalSubmatrix n M S).det) := by sorry
