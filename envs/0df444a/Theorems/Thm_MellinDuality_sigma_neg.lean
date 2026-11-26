-- Prove2me | Theorems.Thm_MellinDuality_sigma_neg
-- name    : MellinDuality.sigma_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:25.010145+00:00
-- url     : https://prove2.me/theorems/bc9caf83-06e6-5d94-b9c1-d3b54b02e01e
-- title:
--   Mellin Duality: sigma neg
-- statement:
--   `σ(-z) = -σ(z)` for `z ≠ 0`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L114-L117
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L114-L117

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

theorem MellinDuality.sigma_neg {z : GaussianInt} (hz : z ≠ 0) : sigma χ (-z) = -sigma χ z := by sorry
