-- Prove2me | Theorems.Thm_GES_isConf_rank_lt
-- name    : GES.isConf_rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:18.755378+00:00
-- url     : https://prove2.me/theorems/f4e5b0f3-eee4-4f5d-95f0-51e2a5e57056
-- title:
--   GES: is Conf rank lt
-- statement:
--   The events of `c` of rank strictly below that of `x`, together with `x`,
--   form a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L156-L186
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L156-L186

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
variable (G)

theorem GES.isConf_rank_lt {c : Set G.Event} (hc : G.isConf c) {x : G.Event} (hx : x ∈ c) :
    G.isConf ({z ∈ c | G.rank c z < G.rank c x} ∪ {x}) := by sorry
