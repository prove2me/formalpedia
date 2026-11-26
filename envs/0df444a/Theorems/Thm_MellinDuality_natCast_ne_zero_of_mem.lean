-- Prove2me | Theorems.Thm_MellinDuality_natCast_ne_zero_of_mem
-- name    : MellinDuality.natCast_ne_zero_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:57.042002+00:00
-- url     : https://prove2.me/theorems/a3160f32-b506-49dd-9277-85d722bebfcf
-- title:
--   Mellin Duality: nat Cast ne zero of mem
-- statement:
--   The Mellin Duality construction uses the nat Cast ne zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L21-L27
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L21-L27

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Parseval
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.natCast_ne_zero_of_mem {n : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2)) : (n : ZMod p) ≠ 0 := by sorry
