-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_sign_property
-- name    : GroupTheoreticShannonCapacity.P0Matrix.p0_sign_property
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:26:05.980854+00:00
-- url     : https://prove2.me/theorems/be4fcf8f-4a4d-4a2a-a488-b9006520f56c
-- title:
--   P0 Matrix: p0 sign property
-- statement:
--   For a P₀-matrix M and nonzero x, ∃i. xᵢ ≠ 0 ∧ (Mx)ᵢ · xᵢ ≥ 0
--
--   Proof by contradiction: If for all j, either x_j = 0 or (Mx)_j * x_j < 0,
--   define d_j = -(Mx)_j / x_j > 0, then A = M + diag(d) satisfies Ax = 0
--   (so det(A) = 0), but by det_add_diagonal, det(A) ≥ ∏_i d_i > 0. Contradiction.
--
--   Note: The general case requires restricting to the support of x and working with
--   the appropriate principal submatrix.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L441-L535
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L441-L535

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.p0_sign_property (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∃ i : Fin n, x i ≠ 0 ∧ (M.mulVec x) i * x i ≥ 0 := by sorry
