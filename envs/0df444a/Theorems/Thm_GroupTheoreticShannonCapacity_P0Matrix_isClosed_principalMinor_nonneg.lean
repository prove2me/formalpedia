-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isClosed_principalMinor_nonneg
-- name    : GroupTheoreticShannonCapacity.P0Matrix.isClosed_principalMinor_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:37.716924+00:00
-- url     : https://prove2.me/theorems/d553741a-d739-49bd-b7d4-b026d3ffc742
-- title:
--   P0 Matrix: is Closed principal Minor nonneg
-- statement:
--   The set of matrices with nonnegative S-principal minor is closed
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L757-L762
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L757-L762

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.isClosed_principalMinor_nonneg (n : ℕ) (S : Finset (Fin n)) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℝ | (principalSubmatrix n M S).det ≥ 0} := by sorry
