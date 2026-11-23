-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_add_scalar_invertible
-- name    : GroupTheoreticShannonCapacity.P0Matrix.p0_add_scalar_invertible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:30:48.550136+00:00
-- url     : https://prove2.me/theorems/0ed4b4ff-19dd-464a-a5fc-9415fdd23680
-- title:
--   P0 Matrix: p0 add scalar invertible
-- statement:
--   If M is P₀ and q > 0, then A = M + qI is invertible
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L540-L564
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L540-L564

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.p0_add_scalar_invertible (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (q : ℝ) (hq : 0 < q) :
    IsUnit (M + q • 1) := by sorry
