-- Prove2me | Theorems.Thm_MellinDuality_sum_fiber_neg
-- name    : MellinDuality.sum_fiber_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:22.817134+00:00
-- url     : https://prove2.me/theorems/438ced94-fc39-414c-b09b-50d4763ce122
-- title:
--   Mellin Duality: sum fiber neg
-- statement:
--   The Mellin Duality construction uses the sum fiber neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L82-L90
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L82-L90

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

theorem MellinDuality.sum_fiber_neg {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (z : GaussianInt) :
    ∑ x ∈ fiber χ (-z), f x = ∑ x ∈ fiber χ z, f (-x) := by sorry
