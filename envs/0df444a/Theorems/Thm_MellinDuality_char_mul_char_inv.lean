-- Prove2me | Theorems.Thm_MellinDuality_char_mul_char_inv
-- name    : MellinDuality.char_mul_char_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:27.863798+00:00
-- url     : https://prove2.me/theorems/3255a630-7947-4878-b73c-0b64f865b56c
-- title:
--   Mellin Duality: char mul char inv
-- statement:
--   The Mellin Duality construction uses the char mul char inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L70-L71
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L70-L71

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}

theorem MellinDuality.char_mul_char_inv {x : ZMod p} (hx : x ≠ 0) : χ x * χ x⁻¹ = 1 := by sorry
