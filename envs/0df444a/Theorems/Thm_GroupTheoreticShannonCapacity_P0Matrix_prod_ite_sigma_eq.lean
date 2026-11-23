-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_prod_ite_sigma_eq
-- name    : GroupTheoreticShannonCapacity.P0Matrix.prod_ite_sigma_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:53.458835+00:00
-- url     : https://prove2.me/theorems/7d7a6197-31e3-4908-95f0-26591f627bf4
-- title:
--   P0 Matrix: prod ite sigma eq
-- statement:
--   Entry of M + diagonal d
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L29-L40
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L29-L40

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.prod_ite_sigma_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    (∏ i ∈ Sᶜ, if σ i = i then (1 : ℝ) else 0) = if ∀ i ∈ Sᶜ, σ i = i then 1 else 0 := by sorry
