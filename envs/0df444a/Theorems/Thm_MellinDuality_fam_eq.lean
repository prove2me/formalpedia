-- Prove2me | Theorems.Thm_MellinDuality_fam_eq
-- name    : MellinDuality.fam_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:27.791702+00:00
-- url     : https://prove2.me/theorems/6571cd10-46ab-4cb5-99d2-307f183861c5
-- title:
--   Mellin Duality: fam eq
-- statement:
--   The family as a product of parity signs.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L54-L58
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L54-L58

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem MellinDuality.fam_eq (χ : MulChar (ZMod p) R) (e : ℕ) (a : ZMod p) :
    fam χ e a = ∑ n ∈ half p, χ n * (parSign n : R) * (parSign (a * n ^ e) : R) := by sorry
