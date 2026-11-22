-- Prove2me | Theorems.Thm_GES_subset_pmapSet
-- name    : GES.subset_pmapSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:48:50.3012+00:00
-- url     : https://prove2.me/theorems/7ba2131e-55d7-4a19-81a4-7cf67c615fa2
-- title:
--   GES: subset pmap Set
-- statement:
--   The GES construction uses the subset pmap Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L193-L196
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L193-L196

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

theorem GES.subset_pmapSet {L' : Type*} {G : GES L} {H : GES L'}
    {φ : G.Event → Option H.Event} {c : Set G.Event}
    {u : G.Event} {x : H.Event} (hu : u ∈ c) (hx : φ u = some x) : x ∈ pmapSet φ c := by sorry
