-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_prod_of_fixing
-- name    : GroupTheoreticShannonCapacity.P0Matrix.prod_of_fixing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:29:32.591798+00:00
-- url     : https://prove2.me/theorems/077b4cf3-d30c-40d3-986c-2c25e842038b
-- title:
--   P0 Matrix: prod of fixing
-- statement:
--   For permutations fixing Sᶜ, the product over S relates to the submatrix
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L141-L164
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L141-L164

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.prod_of_fixing (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (hfix : ∀ i ∈ Sᶜ, σ i = i) :
    ∏ i ∈ S, M (σ i) i =
    ∏ j : Fin S.card, (principalSubmatrix n M S)
      (fixingPermEquiv n S ⟨σ, hfix⟩ j) j := by sorry
