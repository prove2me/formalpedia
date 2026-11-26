-- Prove2me | Theorems.Thm_MellinDuality_multiplier_family_interval
-- name    : MellinDuality.multiplier_family_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:27.217701+00:00
-- url     : https://prove2.me/theorems/905d36f1-53c2-4090-9874-b5431d0bc7c3
-- title:
--   Mellin Duality: multiplier family interval
-- statement:
--   Every member of the multiplier family is a half-interval sum with a `±1` weight:
--   `𝒞_χ^{(2)}(a) = ∑_{n ≤ (p-1)/2} χ(n) (-1)^{n + ⟨a n²⟩}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L213-L217
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L213-L217

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.multiplier_family_interval (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (a : ZMod p) :
    fam χ 2 a = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) *
      (((-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val) : ℤ) : R) := by sorry
