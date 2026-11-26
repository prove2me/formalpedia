-- Prove2me | Theorems.Thm_MellinDuality_char_mul_star
-- name    : MellinDuality.char_mul_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:35.992815+00:00
-- url     : https://prove2.me/theorems/a2f7fdd7-db9d-5719-a6af-568aed4807e9
-- title:
--   Mellin Duality: char mul star
-- statement:
--   The Mellin Duality construction uses the char mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L113-L114
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L113-L114

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem MellinDuality.char_mul_star {x : ZMod p} (hx : x ≠ 0) : χ x * star (χ x) = 1 := by sorry
