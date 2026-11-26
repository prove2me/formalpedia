-- Prove2me | Theorems.Thm_MellinDuality_apply_neg_of_even
-- name    : MellinDuality.apply_neg_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:19.707806+00:00
-- url     : https://prove2.me/theorems/1cd96e17-14b6-51d8-98a1-7a59a3dc09ba
-- title:
--   Mellin Duality: apply neg of even
-- statement:
--   The Mellin Duality construction uses the apply neg of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L89-L91
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L89-L91

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

theorem MellinDuality.apply_neg_of_even (φ : MulChar (ZMod p) R) (hφ : φ (-1) = 1) (x : ZMod p) :
    φ (-x) = φ x := by sorry
