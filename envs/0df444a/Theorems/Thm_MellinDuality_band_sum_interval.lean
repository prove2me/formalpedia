-- Prove2me | Theorems.Thm_MellinDuality_band_sum_interval
-- name    : MellinDuality.band_sum_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:23.473182+00:00
-- url     : https://prove2.me/theorems/74c654d1-6d9a-4421-b0d3-94585e9f6d56
-- title:
--   Mellin Duality: band sum interval
-- statement:
--   `𝒞 = ∑_{n ≤ (p-1)/2} χ(n) ε_n` with `ε_n = (-1)^{⌊n²/p⌋}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L174-L176
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L174-L176

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.band_sum_interval (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) :
    bandSumPow χ 2 = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) * (eps p n : R) := by sorry
