-- Prove2me | Theorems.Thm_MellinDuality_parSign_sq
-- name    : MellinDuality.parSign_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:03.888033+00:00
-- url     : https://prove2.me/theorems/f4313701-53d0-5e62-81d6-65b3ba1385e9
-- title:
--   Mellin Duality: par Sign sq
-- statement:
--   The Mellin Duality construction uses the par Sign sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L46-L47
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L46-L47

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem MellinDuality.parSign_sq (x : ZMod p) : parSign x * parSign x = 1 := by sorry
