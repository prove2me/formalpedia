-- Prove2me | Theorems.Thm_MellinDuality_hp2_of
-- name    : MellinDuality.hp2_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:58.578668+00:00
-- url     : https://prove2.me/theorems/00f42538-7822-43aa-bbd2-95919fd2df4f
-- title:
--   Mellin Duality: hp2 of
-- statement:
--   The Mellin Duality construction uses the hp2 of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L42-L42
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L42-L42

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem MellinDuality.hp2_of (hp8 : p % 8 = 5) : p ≠ 2 := by sorry
