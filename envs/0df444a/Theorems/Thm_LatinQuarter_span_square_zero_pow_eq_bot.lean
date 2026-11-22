-- Prove2me | Theorems.Thm_LatinQuarter_span_square_zero_pow_eq_bot
-- name    : LatinQuarter.span_square_zero_pow_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:32.460486+00:00
-- url     : https://prove2.me/theorems/90448b5f-f14f-4ebd-9a0f-7f4bae766032
-- title:
--   Latin Quarter: span square zero pow eq bot
-- statement:
--   The Latin Quarter construction uses the span square zero pow eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/SquareZero.lean#L46-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/SquareZero.lean#L46-L62

module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Operations
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Pointwise
variable {R : Type*} [CommRing R]

theorem LatinQuarter.span_square_zero_pow_eq_bot
    {κ : Type*} [Fintype κ] (z : κ → R)
    (hz : ∀ j, z j * z j = 0) {d : ℕ}
    (hd : Fintype.card κ < d) :
    Ideal.span (Set.range z) ^ d = ⊥ := by sorry
