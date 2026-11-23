-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_principalSubmatrix
-- name    : GroupTheoreticShannonCapacity.P0Matrix.isP0_principalSubmatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:30:36.155804+00:00
-- url     : https://prove2.me/theorems/1a4248f7-84db-4a7a-97fd-c08538269e07
-- title:
--   P0 Matrix: is P0 principal Submatrix
-- statement:
--   A principal submatrix of a P₀ matrix is P₀
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L319-L364
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L319-L364

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.isP0_principalSubmatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (S : Finset (Fin n)) : IsP0Matrix S.card (principalSubmatrix n M S) := by sorry
