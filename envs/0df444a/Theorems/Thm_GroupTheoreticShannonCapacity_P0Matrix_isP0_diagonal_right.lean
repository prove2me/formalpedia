-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_diagonal_right
-- name    : GroupTheoreticShannonCapacity.P0Matrix.isP0_diagonal_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:08.309969+00:00
-- url     : https://prove2.me/theorems/93f61db0-f6d9-43d4-9fca-fa50f13394e7
-- title:
--   P0 Matrix: is P0 diagonal right
-- statement:
--   P₀ is preserved under right multiplication by nonnegative diagonal matrices
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L731-L741
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L731-L741

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.isP0_diagonal_right (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsP0Matrix n (M * diagonal d) := by sorry
