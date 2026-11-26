-- Prove2me | Theorems.Thm_MellinDuality_bandSum_eq_Icc
-- name    : MellinDuality.bandSum_eq_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:22.411836+00:00
-- url     : https://prove2.me/theorems/a64a3b2b-08c8-53d3-9d08-cc239b8a63a3
-- title:
--   Mellin Duality: band Sum eq Icc
-- statement:
--   `𝒞 = ∑_{n ≤ N} χ(n) ε_n`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L83-L103
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L83-L103

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.bandSum_eq_Icc (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) :
    bandSumPow χ 2 = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) * (eps p n : R) := by sorry
