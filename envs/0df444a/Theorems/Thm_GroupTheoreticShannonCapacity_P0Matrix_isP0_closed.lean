-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_closed
-- name    : GroupTheoreticShannonCapacity.P0Matrix.isP0_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:36.039653+00:00
-- url     : https://prove2.me/theorems/027f8f10-b157-4fd3-bfb8-12b77ddd9fe1
-- title:
--   P0 Matrix: is P0 closed
-- statement:
--   P₀ property is closed (limit of P₀ matrices is P₀)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L765-L773
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L765-L773

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.isP0_closed (n : ℕ) : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | IsP0Matrix n M} := by sorry
