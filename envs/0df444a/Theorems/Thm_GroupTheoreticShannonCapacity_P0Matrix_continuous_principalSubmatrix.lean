-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_continuous_principalSubmatrix
-- name    : GroupTheoreticShannonCapacity.P0Matrix.continuous_principalSubmatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:35.604526+00:00
-- url     : https://prove2.me/theorems/d4f32c66-79c5-4dd4-bccd-909dd30a6f23
-- title:
--   P0 Matrix: continuous principal Submatrix
-- statement:
--   The map sending a matrix to its principal submatrix is continuous
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L744-L749
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L744-L749

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.continuous_principalSubmatrix (n : ℕ) (S : Finset (Fin n)) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => principalSubmatrix n M S) := by sorry
