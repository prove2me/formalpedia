-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_diagonal_left
-- name    : GroupTheoreticShannonCapacity.P0Matrix.isP0_diagonal_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:10.048111+00:00
-- url     : https://prove2.me/theorems/e06a76b1-f86e-4d80-a687-1d2474762cb8
-- title:
--   P0 Matrix: is P0 diagonal left
-- statement:
--   P₀ is preserved under conjugation by positive diagonal matrices
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L718-L728
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L718-L728

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.isP0_diagonal_left (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsP0Matrix n (diagonal d * M) := by sorry
