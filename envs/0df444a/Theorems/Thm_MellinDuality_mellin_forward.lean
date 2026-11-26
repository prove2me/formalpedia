-- Prove2me | Theorems.Thm_MellinDuality_mellin_forward
-- name    : MellinDuality.mellin_forward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:58.932977+00:00
-- url     : https://prove2.me/theorems/7e8a7578-02ab-42c5-8614-a53a4706d51c
-- title:
--   Mellin Duality: mellin forward
-- statement:
--   **Mellin duality** (Theorem 3.1 of Paper II, forward form, for the exponent `2m`). For an odd
--   prime `p`, an odd character `χ` and any character `ψ` with values in a commutative ring,
--   `2 ∑_a ψ̄(a) 𝒞_χ^{(2m)}(a) = 𝒢(ψ̄) 𝒢(χ ψ^{2m})`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L74-L91
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L74-L91

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

theorem MellinDuality.mellin_forward (hp2 : p ≠ 2) (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) (m : ℕ) :
    2 * ∑ a, ψ⁻¹ a * fam χ (2 * m) a = G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by sorry
