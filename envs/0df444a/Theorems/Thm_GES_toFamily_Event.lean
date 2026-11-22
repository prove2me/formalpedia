-- Prove2me | Theorems.Thm_GES_toFamily_Event
-- name    : GES.toFamily_Event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:24.451056+00:00
-- url     : https://prove2.me/theorems/dfa2dc59-d614-4e74-b004-74515ffc32f3
-- title:
--   GES: to Family Event
-- statement:
--   The GES construction uses the to Family Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L283-L283
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L283-L283

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

theorem GES.toFamily_Event : G.toFamily.Event = G.Event := by sorry

attribute [defeq] GES.toFamily_Event
