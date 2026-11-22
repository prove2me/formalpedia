-- Prove2me | Theorems.Thm_GES_isConf_insert_pmap
-- name    : GES.isConf_insert_pmap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:38:06.488841+00:00
-- url     : https://prove2.me/theorems/cf095e9f-b651-4161-bde0-d5cb5c2ea8be
-- title:
--   GES: is Conf insert pmap
-- statement:
--   Conversely, an event whose image is enabled extends a configuration, provided
--   enabling sets pull back.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L239-L273
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L239-L273

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

theorem GES.isConf_insert_pmap {L' : Type*} {G : GES L} {H : GES L'}
    (φ : G.Event → Option H.Event)
    {c : Set G.Event} {u : G.Event} {x : H.Event} (hc : G.isConf c) (hφ : φ u = some x)
    (hcon : G.Consistent (c ∪ {u}))
    (hback : ∀ Y : Finset H.Event, (∀ y ∈ Y, y ∈ pmapSet φ c) → H.enable Y x →
      ∃ X : Finset G.Event, (X : Set G.Event) ⊆ c ∧ G.enable X u)
    (hx : H.isConf (pmapSet φ c ∪ {x})) : G.isConf (c ∪ {u}) := by sorry
