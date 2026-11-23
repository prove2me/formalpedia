-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_sum_fixing_eq_det
-- name    : GroupTheoreticShannonCapacity.P0Matrix.sum_fixing_eq_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:29:47.190798+00:00
-- url     : https://prove2.me/theorems/be8e6647-eaf4-4857-9962-8af93471e638
-- title:
--   P0 Matrix: sum fixing eq det
-- statement:
--   Sum over permutations fixing Sᶜ equals det of submatrix
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L167-L199
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L167-L199

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.sum_fixing_eq_det (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    ∑ σ ∈ Finset.filter (fun σ => ∀ i ∈ Sᶜ, σ i = i) Finset.univ,
      (Equiv.Perm.sign σ : ℝ) * ∏ i ∈ S, M (σ i) i =
    (principalSubmatrix n M S).det := by sorry
