-- Prove2me | Theorems.Thm_GES_pmapSet_mono
-- name    : GES.pmapSet_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:48:57.773316+00:00
-- url     : https://prove2.me/theorems/9f4349e2-41c1-4f44-b078-dd45ebec3e21
-- title:
--   GES: pmap Set mono
-- statement:
--   The GES construction uses the pmap Set mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L198-L201
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L198-L201

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

theorem GES.pmapSet_mono {L' : Type*} {G : GES L} {H : GES L'}
    {φ : G.Event → Option H.Event} {c d : Set G.Event}
    (h : c ⊆ d) : pmapSet φ c ⊆ pmapSet φ d := by sorry
