-- Prove2me | Theorems.Thm_MellinDuality_char_mul_self
-- name    : MellinDuality.char_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:11.737465+00:00
-- url     : https://prove2.me/theorems/fe715903-ac41-4f17-afad-76029f2c4fb7
-- title:
--   Mellin Duality: char mul self
-- statement:
--   The Mellin Duality construction uses the char mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L116-L118
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L116-L118

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

theorem MellinDuality.char_mul_self {r : ℕ} (hr : (r : ZMod p) ≠ 0) :
    χ r * χ r = ((legendreSym p r : ℤ) : GaussianInt) := by sorry
