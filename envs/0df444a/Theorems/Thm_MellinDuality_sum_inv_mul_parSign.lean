-- Prove2me | Theorems.Thm_MellinDuality_sum_inv_mul_parSign
-- name    : MellinDuality.sum_inv_mul_parSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:54.451811+00:00
-- url     : https://prove2.me/theorems/deab8fc1-4e07-5cc0-94a4-9de56e0b25a8
-- title:
--   Mellin Duality: sum inv mul par Sign
-- statement:
--   The substitution `b = a c`: `∑_a ψ̄(a) s(a c) = ψ(c) 𝒢(ψ̄)` for `c ≠ 0`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L61-L69
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L61-L69

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

theorem MellinDuality.sum_inv_mul_parSign (ψ : MulChar (ZMod p) R) {c : ZMod p} (hc : c ≠ 0) :
    ∑ a, ψ⁻¹ a * (parSign (a * c) : R) = ψ c * G ψ⁻¹ := by sorry
