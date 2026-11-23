-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_sign_of_fixing
-- name    : GroupTheoreticShannonCapacity.P0Matrix.sign_of_fixing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:29:11.121901+00:00
-- url     : https://prove2.me/theorems/ecd92672-82ae-40e9-97aa-28daba14d9e4
-- title:
--   P0 Matrix: sign of fixing
-- statement:
--   For permutations fixing Sᶜ, the sign equals the sign of the induced permutation on S
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L91-L106
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L91-L106

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.sign_of_fixing (n : ℕ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hfix : ∀ i ∈ Sᶜ, σ i = i) :
    Equiv.Perm.sign σ = Equiv.Perm.sign (fixingPermEquiv n S ⟨σ, hfix⟩) := by sorry
