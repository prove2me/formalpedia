-- Prove2me | Theorems.Thm_MellinDuality_neg_mem_half_iff
-- name    : MellinDuality.neg_mem_half_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:24.630995+00:00
-- url     : https://prove2.me/theorems/93b0bc27-ab80-4ee3-80b7-ca64c421ba75
-- title:
--   Mellin Duality: neg mem half iff
-- statement:
--   The Mellin Duality construction uses the neg mem half iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L54-L59
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L54-L59

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.neg_mem_half_iff (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : -x ∈ half p ↔ x ∉ half p := by sorry
