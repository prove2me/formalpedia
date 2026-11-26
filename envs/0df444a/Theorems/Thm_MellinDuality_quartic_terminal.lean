-- Prove2me | Theorems.Thm_MellinDuality_quartic_terminal
-- name    : MellinDuality.quartic_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:06.154158+00:00
-- url     : https://prove2.me/theorems/cbb16b09-70f7-5ac1-bfe6-55fca95aadba
-- title:
--   Mellin Duality: quartic terminal
-- statement:
--   **The terminal values of the exponent family** (Corollary 3.2 of Paper II, quartic case): if
--   `(p - 1) ∣ 4m` then `𝒞_{2m} = -γ` when `(p - 1) ∣ 2m` and `𝒞_{2m} = -γ̄` otherwise; with
--   `γ = (1 - 2i)β` these are `-(1 - 2i)β` and its conjugate.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L259-L268
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L259-L268

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ

theorem MellinDuality.quartic_terminal {m : ℕ} (hm : 1 ≤ m) (h4 : p - 1 ∣ 4 * m) :
    bandSumPow χ (2 * m) = if p - 1 ∣ 2 * m then -gamma χ else -star (gamma χ) := by sorry
