-- Prove2me | Theorems.Thm_MellinDuality_exponent_collapse_two
-- name    : MellinDuality.exponent_collapse_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:00.437817+00:00
-- url     : https://prove2.me/theorems/4e826423-c7f8-4588-9d13-abbcafc4da48
-- title:
--   Mellin Duality: exponent collapse two
-- statement:
--   **The exponent family collapses** (Corollary 3.2, second case): if `(p - 1) ∣ 4m` but
--   `(p - 1) ∤ 2m`, then `2 𝒞_{2m} = -𝒢(χ · (·/p))`. (For the quartic character `χ (·/p) = χ̄`.)
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L140-L193
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L140-L193

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

theorem MellinDuality.exponent_collapse_two (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) {m : ℕ}
    (h4 : p - 1 ∣ 4 * m) (h2 : ¬ p - 1 ∣ 2 * m) :
    2 * bandSumPow χ (2 * m) = -G (χ * quadR p R) := by sorry
