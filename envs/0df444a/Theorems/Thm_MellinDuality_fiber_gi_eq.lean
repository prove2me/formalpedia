-- Prove2me | Theorems.Thm_MellinDuality_fiber_gi_eq
-- name    : MellinDuality.fiber_gi_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:20.102118+00:00
-- url     : https://prove2.me/theorems/fb7ff923-2a89-4078-9717-7e058adb107b
-- title:
--   Mellin Duality: fiber gi eq
-- statement:
--   With `χ(2) = i`, `fiber χ i = 2H`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L283-L293
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L283-L293

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
omit hχ

theorem MellinDuality.fiber_gi_eq (hpin : χ 2 = gi) : fiber χ gi = (fiber χ 1).image (2 * ·) := by sorry
