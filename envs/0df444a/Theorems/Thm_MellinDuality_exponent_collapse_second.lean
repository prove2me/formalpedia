-- Prove2me | Theorems.Thm_MellinDuality_exponent_collapse_second
-- name    : MellinDuality.exponent_collapse_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:00:18.420882+00:00
-- url     : https://prove2.me/theorems/73a36579-281a-44c0-ad8c-f9535fbb047a
-- title:
--   Mellin Duality: exponent collapse second
-- statement:
--   **The collapse** (Corollary 3.2): if `(p - 1) ∣ 4m` and `(p - 1) ∤ 2m`, then
--   `2 𝒞_{2m} = -𝒢(χ (·/p))`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L98-L101
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L98-L101

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.exponent_collapse_second {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (h4 : p - 1 ∣ 4 * m) (h2 : ¬ p - 1 ∣ 2 * m) :
    2 * bandSumPow χ (2 * m) = -G (χ * quadR p R) := by sorry
