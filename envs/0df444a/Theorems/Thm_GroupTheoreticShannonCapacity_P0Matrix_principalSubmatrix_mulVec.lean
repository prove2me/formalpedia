-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_mulVec
-- name    : GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_mulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:30:39.334742+00:00
-- url     : https://prove2.me/theorems/ab6302be-2e77-4230-85f1-07a7f5d918ef
-- title:
--   P0 Matrix: principal Submatrix mul Vec
-- statement:
--   For a vector x with support in S, the principal submatrix product equals the original product.
--   Specifically, (M_S · x_S)_i = (M · x)_{S(i)} when x is zero outside S.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L368-L405
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L368-L405

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_mulVec (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (x : Fin n → ℝ) (hx_supp : ∀ i, i ∉ S → x i = 0) (i : Fin S.card) :
    (principalSubmatrix n M S).mulVec (x ∘ S.orderEmbOfFin rfl) i =
    (M.mulVec x) (S.orderEmbOfFin rfl i) := by sorry
