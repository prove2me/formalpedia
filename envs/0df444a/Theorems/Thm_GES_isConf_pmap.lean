-- Prove2me | Theorems.Thm_GES_isConf_pmap
-- name    : GES.isConf_pmap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:31.73627+00:00
-- url     : https://prove2.me/theorems/46939b35-f820-445a-a9eb-1a3279f8afb0
-- title:
--   GES: is Conf pmap
-- statement:
--   Configurations transfer along a partial map that carries enabling sets to
--   enabling sets.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L205-L235
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L205-L235

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

theorem GES.isConf_pmap {L' : Type*} {G : GES L} {H : GES L'}
    (φ : G.Event → Option H.Event)
    (hcon : ∀ {c : Set G.Event}, G.Consistent c → H.Consistent (pmapSet φ c))
    (hen : ∀ {X : Finset G.Event} {u : G.Event} {x : H.Event},
      G.enable X u → φ u = some x →
      ∃ Y : Finset H.Event, (∀ y ∈ Y, y ∈ pmapSet φ (X : Set G.Event)) ∧ H.enable Y x)
    {c : Set G.Event} (hc : G.isConf c) : H.isConf (pmapSet φ c) := by sorry
