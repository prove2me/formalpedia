-- Prove2me | Theorems.Thm_GES_toFamily_Config
-- name    : GES.toFamily_Config
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:19.264087+00:00
-- url     : https://prove2.me/theorems/7c09c8cd-308d-4d97-88c4-b51cec9ee70d
-- title:
--   GES: to Family Config
-- statement:
--   The GES construction uses the to Family Config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L284-L284
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean#L284-L284

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

theorem GES.toFamily_Config : G.toFamily.Config = G.isConf := by sorry

attribute [defeq] GES.toFamily_Config
