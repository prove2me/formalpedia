-- Prove2me | Theorems.Thm_MellinDuality_val_two_mul_of_mem_half
-- name    : MellinDuality.val_two_mul_of_mem_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:12.64551+00:00
-- url     : https://prove2.me/theorems/bef34903-3095-4c7b-884b-dec8cf2ae293
-- title:
--   Mellin Duality: val two mul of mem half
-- statement:
--   The Mellin Duality construction uses the val two mul of mem half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L118-L122
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L118-L122

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem MellinDuality.val_two_mul_of_mem_half {n : ZMod p} (hn : n ∈ half p) : (2 * n).val = 2 * n.val := by sorry
