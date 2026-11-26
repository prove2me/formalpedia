-- Prove2me | Theorems.Thm_MellinDuality_mellin_duality
-- name    : MellinDuality.mellin_duality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:58:49.639642+00:00
-- url     : https://prove2.me/theorems/9089d54a-6084-429b-99c4-e29215f03326
-- title:
--   Mellin Duality: mellin duality
-- statement:
--   **Mellin duality** (Theorem 3.1, with the exponent `2m` of Corollary 3.2). For an odd prime `p`, an
--   odd character `χ` and any character `ψ` with values in a commutative ring,
--   `2 ∑_a ψ̄(a) 𝒞_χ^{(2m)}(a) = 𝒢(ψ̄) 𝒢(χ ψ^{2m})`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L49-L51
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L49-L51

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mellin_duality {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    (m : ℕ) : 2 * ∑ a, ψ⁻¹ a * fam χ (2 * m) a = G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by sorry
