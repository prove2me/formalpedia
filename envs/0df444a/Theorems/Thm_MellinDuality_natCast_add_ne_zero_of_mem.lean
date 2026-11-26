-- Prove2me | Theorems.Thm_MellinDuality_natCast_add_ne_zero_of_mem
-- name    : MellinDuality.natCast_add_ne_zero_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:00.707961+00:00
-- url     : https://prove2.me/theorems/f62a2a60-a072-5b68-b211-37ccaed0eb2b
-- title:
--   Mellin Duality: nat Cast add ne zero of mem
-- statement:
--   The Mellin Duality construction uses the nat Cast add ne zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L27-L34
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L27-L34

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.natCast_add_ne_zero_of_mem {n n' : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2))
    (hn' : n' ∈ Icc 1 ((p - 1) / 2)) : (n' : ZMod p) ≠ -(n : ZMod p) := by sorry
