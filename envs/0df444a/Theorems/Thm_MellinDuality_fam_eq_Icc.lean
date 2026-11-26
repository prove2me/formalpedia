-- Prove2me | Theorems.Thm_MellinDuality_fam_eq_Icc
-- name    : MellinDuality.fam_eq_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:58.371156+00:00
-- url     : https://prove2.me/theorems/682e87aa-8d52-4e1d-bef9-936a1b5d8f8f
-- title:
--   Mellin Duality: fam eq Icc
-- statement:
--   Every member of the multiplier family is a half-interval sum with a `±1` weight:
--   `𝒞_χ(a) = ∑_{n ≤ N} χ(n) (-1)^{n + ⟨a n²⟩}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L86-L107
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L86-L107

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.fam_eq_Icc (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (a : ZMod p) :
    fam χ 2 a = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) *
      (((-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val) : ℤ) : R) := by sorry
