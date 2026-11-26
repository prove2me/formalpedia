-- Prove2me | Theorems.Thm_MellinDuality_fam_one_eq_bandSumPow
-- name    : MellinDuality.fam_one_eq_bandSumPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:12.058805+00:00
-- url     : https://prove2.me/theorems/41159cfa-e558-5907-adc9-ba1e5e442f54
-- title:
--   Mellin Duality: fam one eq band Sum Pow
-- statement:
--   **The parity dictionary**: `𝒞_χ^{(e)}(1) = ∑_{0 < n < p/2} χ(n) (-1)^{⌊n^e/p⌋}` for `e ≥ 1`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L94-L115
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L94-L115

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

theorem MellinDuality.fam_one_eq_bandSumPow (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) {e : ℕ} (he : 1 ≤ e) :
    fam χ e 1 = bandSumPow χ e := by sorry
