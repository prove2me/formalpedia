-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_empty_det
-- name    : GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_empty_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:30:22.531394+00:00
-- url     : https://prove2.me/theorems/6e4114b4-0599-49ee-a086-9cf98a23e13f
-- title:
--   P0 Matrix: principal Submatrix empty det
-- statement:
--   The determinant of the empty principal submatrix is 1
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L313-L316
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L313-L316

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_empty_det (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (principalSubmatrix n M ∅).det = 1 := by sorry
