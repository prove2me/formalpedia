-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_min_distance_bound
-- name    : GroupTheoreticShannonCapacity.P0Matrix.p0_min_distance_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:31:25.934166+00:00
-- url     : https://prove2.me/theorems/675f9367-5c29-4d62-a0e7-c3579f71e276
-- title:
--   P0 Matrix: p0 min distance bound
-- statement:
--   If M is P₀ and q > 0, then λ_∞(L(M + qI)) ≥ q
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L567-L667
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L567-L667

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.p0_min_distance_bound (n : ℕ) [NeZero n] (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsP0Matrix n M) (q : ℝ) (hq : 0 < q) :
    Lattice.minDistance n (Lattice.latticeOfMatrix n (M + q • 1)) ≥ q := by sorry
