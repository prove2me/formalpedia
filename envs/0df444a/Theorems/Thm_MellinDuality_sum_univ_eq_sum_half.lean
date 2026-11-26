-- Prove2me | Theorems.Thm_MellinDuality_sum_univ_eq_sum_half
-- name    : MellinDuality.sum_univ_eq_sum_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:37.058244+00:00
-- url     : https://prove2.me/theorems/bdb49e69-5b31-51bd-93d5-e7ba3371e921
-- title:
--   Mellin Duality: sum univ eq sum half
-- statement:
--   A sum over `ZMod p` of a function vanishing at `0` is the sum over the half system of
--   `f(n) + f(-n)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L63-L81
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L63-L81

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.sum_univ_eq_sum_half (hp2 : p ≠ 2) {M : Type*} [AddCommMonoid M] (f : ZMod p → M)
    (h0 : f 0 = 0) : ∑ x, f x = ∑ n ∈ half p, (f n + f (-n)) := by sorry
