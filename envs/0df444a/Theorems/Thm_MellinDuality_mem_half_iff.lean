-- Prove2me | Theorems.Thm_MellinDuality_mem_half_iff
-- name    : MellinDuality.mem_half_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:49.004938+00:00
-- url     : https://prove2.me/theorems/f215b36b-f511-4073-b544-e39909839a4b
-- title:
--   Mellin Duality: mem half iff
-- statement:
--   The Mellin Duality construction uses the mem half iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L49-L49
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L49-L49

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mem_half_iff {x : ZMod p} : x ∈ half p ↔ 2 * x.val < p := by sorry
