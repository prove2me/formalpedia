-- Prove2me | Theorems.Thm_MellinDuality_exponent_collapse_first
-- name    : MellinDuality.exponent_collapse_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:40.861967+00:00
-- url     : https://prove2.me/theorems/9327b1be-39a2-59d2-af3b-9127df174cbd
-- title:
--   Mellin Duality: exponent collapse first
-- statement:
--   **The collapse** (Corollary 3.2): if `(p - 1) ∣ 2m`, then `2 𝒞_{2m} = -𝒢(χ)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L92-L94
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L92-L94

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.exponent_collapse_first {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (hm : 1 ≤ m) (hdiv : p - 1 ∣ 2 * m) : 2 * bandSumPow χ (2 * m) = -G χ := by sorry
