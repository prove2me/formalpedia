-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_add_pos_diagonal_det_pos
-- name    : GroupTheoreticShannonCapacity.P0Matrix.p0_add_pos_diagonal_det_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:30:27.670662+00:00
-- url     : https://prove2.me/theorems/17184c62-607c-4df6-a7c7-c6b361255f0a
-- title:
--   P0 Matrix: p0 add pos diagonal det pos
-- statement:
--   Key corollary: For P₀ matrix M with positive diagonal d, det(M + diag(d)) > 0.
--   This follows from det_add_diagonal since:
--   - Term for S = ∅: det(M_∅) * ∏_i d_i = 1 * ∏_i d_i > 0
--   - All other terms: det(M_S) ≥ 0 (P₀) and ∏_{i∉S} d_i > 0
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L411-L431
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L411-L431

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.p0_add_pos_diagonal_det_pos (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsP0Matrix n M) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    0 < (M + diagonal d).det := by sorry
