-- Prove2me | Theorems.Thm_MellinDuality_G_eq_two_mul_half
-- name    : MellinDuality.G_eq_two_mul_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:56.557549+00:00
-- url     : https://prove2.me/theorems/61f5a1c2-4ae9-5a67-b61a-b3c21055ed96
-- title:
--   Mellin Duality: G eq two mul half
-- statement:
--   For odd `φ`, `𝒢(φ) = 2 ∑_{0 < n < p/2} φ(n) (-1)^n`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L94-L101
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L94-L101

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

theorem MellinDuality.G_eq_two_mul_half (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) :
    G φ = 2 * ∑ n ∈ half p, φ n * (parSign n : R) := by sorry
