-- Prove2me | Theorems.Thm_MellinDuality_G_eq_two_mul_char_two_mul_half
-- name    : MellinDuality.G_eq_two_mul_char_two_mul_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:20.898807+00:00
-- url     : https://prove2.me/theorems/1bc60fe3-a4be-4955-803b-648ac95b30bd
-- title:
--   Mellin Duality: G eq two mul char two mul half
-- statement:
--   `𝒢(ψ) = 2 ψ(2) ∑_{0 < m < p/2} ψ(m)` for odd `ψ`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L131-L147
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L131-L147

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

theorem MellinDuality.G_eq_two_mul_char_two_mul_half (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R)
    (hψ : ψ (-1) = -1) : G ψ = 2 * ψ 2 * ∑ n ∈ half p, ψ n := by sorry
