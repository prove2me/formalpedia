-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_det_add_diagonal
-- name    : GroupTheoreticShannonCapacity.P0Matrix.det_add_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:29:54.684306+00:00
-- url     : https://prove2.me/theorems/859728c4-78fb-4bcc-b034-60fd26390d23
-- title:
--   P0 Matrix: det add diagonal
-- statement:
--   det(M + diag(d₁,...,dₙ)) = Σ_{S⊆[n]} det(M_S) ∏_{i∉S} dᵢ
--
--   This follows from multilinearity of the determinant. The proof proceeds by:
--   1. Viewing det as multilinear in columns
--   2. Expanding (M + diag(d)) column-wise: column j = M[:,j] + d_j * e_j
--   3. Each term in the expansion corresponds to choosing M[:,j] or d_j*e_j for each column
--   4. The term for subset S (choosing M columns for S, diagonal for Sᶜ) equals det(M_S) * ∏_{i∉S} d_i
--
--   The formal proof uses the Leibniz formula and careful analysis of which permutations
--   contribute to each subset.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L212-L308
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L212-L308

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.det_add_diagonal (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (M + diagonal d).det =
    ∑ S : Finset (Fin n), (principalSubmatrix n M S).det * ∏ i ∈ Sᶜ, d i := by sorry
