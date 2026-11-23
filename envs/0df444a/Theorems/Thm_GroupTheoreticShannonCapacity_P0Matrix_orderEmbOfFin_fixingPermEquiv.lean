-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_orderEmbOfFin_fixingPermEquiv
-- name    : GroupTheoreticShannonCapacity.P0Matrix.orderEmbOfFin_fixingPermEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:29:13.105135+00:00
-- url     : https://prove2.me/theorems/644be8a8-59f2-44f0-9039-fa7b0dbd3e61
-- title:
--   P0 Matrix: order Emb Of Fin fixing Perm Equiv
-- statement:
--   The key relation: orderEmbOfFin commutes with fixingPermEquiv and σ
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L109-L138
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean#L109-L138

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset

theorem GroupTheoreticShannonCapacity.P0Matrix.orderEmbOfFin_fixingPermEquiv (n : ℕ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hfix : ∀ i ∈ Sᶜ, σ i = i) (j : Fin S.card) :
    S.orderEmbOfFin rfl (fixingPermEquiv n S ⟨σ, hfix⟩ j) = σ (S.orderEmbOfFin rfl j) := by sorry
