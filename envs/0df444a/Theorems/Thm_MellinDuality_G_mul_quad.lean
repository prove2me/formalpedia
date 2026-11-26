-- Prove2me | Theorems.Thm_MellinDuality_G_mul_quad
-- name    : MellinDuality.G_mul_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:01.317402+00:00
-- url     : https://prove2.me/theorems/7f03f37e-154d-54e8-ab5b-d588332d0fe5
-- title:
--   Mellin Duality: G mul quad
-- statement:
--   `𝒢(χ (·/p)) = 𝒢(χ̄)`: for the quartic character, `χ (·/p) = χ̄`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L242-L254
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L242-L254

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
omit hp8

theorem MellinDuality.G_mul_quad : G (χ * quadR p GaussianInt) = star (G χ) := by sorry
