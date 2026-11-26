-- Prove2me | Theorems.Thm_MellinDuality_exponent_terminal_values
-- name    : MellinDuality.exponent_terminal_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:00:59.815388+00:00
-- url     : https://prove2.me/theorems/07b58fa3-7f29-5568-8ccb-1904c6dd16be
-- title:
--   Mellin Duality: exponent terminal values
-- statement:
--   **The terminal values** (Corollary 3.2, quartic case): if `(p - 1) ∣ 4m` then `𝒞_{2m} = -γ`
--   when `(p - 1) ∣ 2m` and `𝒞_{2m} = -γ̄` otherwise.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L125-L128
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L125-L128

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.exponent_terminal_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {m : ℕ} (hm : 1 ≤ m) (h4 : p - 1 ∣ 4 * m) :
    bandSumPow χ (2 * m) = if p - 1 ∣ 2 * m then -gamma χ else -star (gamma χ) := by sorry
