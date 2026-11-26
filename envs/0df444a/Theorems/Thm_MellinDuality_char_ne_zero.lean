-- Prove2me | Theorems.Thm_MellinDuality_char_ne_zero
-- name    : MellinDuality.char_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:50.711882+00:00
-- url     : https://prove2.me/theorems/fb9ed78f-908a-468f-bbac-52c2f0f42231
-- title:
--   Mellin Duality: char ne zero
-- statement:
--   The Mellin Duality construction uses the char ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L79-L80
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L79-L80

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
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8

theorem MellinDuality.char_ne_zero {x : ZMod p} (hx : x ≠ 0) : χ x ≠ 0 := by sorry
