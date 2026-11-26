-- Prove2me | Theorems.Thm_MellinDuality_sum_univ_fibers
-- name    : MellinDuality.sum_univ_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:23.818918+00:00
-- url     : https://prove2.me/theorems/d69a3b19-1a94-4365-9776-e670eabe14d2
-- title:
--   Mellin Duality: sum univ fibers
-- statement:
--   A sum over `ZMod p` of a function vanishing at `0` splits over the four fibres.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L94-L111
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L94-L111

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

theorem MellinDuality.sum_univ_fibers {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (h0 : f 0 = 0) :
    ∑ x, f x = ∑ x ∈ fiber χ 1, f x + ∑ x ∈ fiber χ gi, f x + ∑ x ∈ fiber χ (-1), f x +
      ∑ x ∈ fiber χ (-gi), f x := by sorry
