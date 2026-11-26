-- Prove2me | Theorems.Thm_MellinDuality_mul_pow_two_mul_odd
-- name    : MellinDuality.mul_pow_two_mul_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:31.121287+00:00
-- url     : https://prove2.me/theorems/5b50a44c-9d71-56a5-ac35-22d7a3544b7d
-- title:
--   Mellin Duality: mul pow two mul odd
-- statement:
--   `χ ψ^{2m}` is odd when `χ` is.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L46-L48
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L46-L48

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

theorem MellinDuality.mul_pow_two_mul_odd (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) (m : ℕ) :
    (χ * ψ ^ (2 * m)) (-1) = -1 := by sorry
