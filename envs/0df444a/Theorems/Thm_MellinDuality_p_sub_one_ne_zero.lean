-- Prove2me | Theorems.Thm_MellinDuality_p_sub_one_ne_zero
-- name    : MellinDuality.p_sub_one_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:47.071247+00:00
-- url     : https://prove2.me/theorems/75af10ac-77b5-5d08-9659-0d74f9c9bba9
-- title:
--   Mellin Duality: p sub one ne zero
-- statement:
--   The Mellin Duality construction uses the p sub one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L202-L203
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L202-L203

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.p_sub_one_ne_zero : (p : ℂ) - 1 ≠ 0 := by sorry
