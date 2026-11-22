-- Prove2me | Theorems.Thm_GES_exists_enabling
-- name    : GES.exists_enabling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:38:17.091595+00:00
-- url     : https://prove2.me/theorems/d5e627e7-cb46-46f2-a96c-fa88c2f10b90
-- title:
--   GES: exists enabling
-- statement:
--   Every event of a configuration has an enabling set inside it.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L93-L100
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L93-L100

import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Minimal
import Definitions.Def_EventStructures_General_Basic
set_option autoImplicit true
open GES
variable {L : Type*} (G : GES L)
local infix:50 " ⊢ " => G.enable
variable {G}
variable (G)
variable {G}

theorem GES.exists_enabling {x : Set G.Event} (hx : G.isConf x) {e : G.Event} (he : e ∈ x) :
    ∃ Y : Finset G.Event, (Y ⊢ e) ∧ ↑Y ⊆ x := by sorry
