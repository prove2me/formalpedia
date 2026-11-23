-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_smul_pos
-- name    : GroupTheoreticShannonCapacity.P0Matrix.isP0_smul_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:09.480254+00:00
-- url     : https://prove2.me/theorems/60bc603c-3ca9-45ff-8c9c-b8d9ade87b3d
-- title:
--   P0 Matrix: is P0 smul pos
-- statement:
--   P₀ is preserved under multiplication by positive scalars
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L680-L687
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L680-L687

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.isP0_smul_pos (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (c : ℝ) (hc : 0 < c) : IsP0Matrix n (c • M) := by sorry
