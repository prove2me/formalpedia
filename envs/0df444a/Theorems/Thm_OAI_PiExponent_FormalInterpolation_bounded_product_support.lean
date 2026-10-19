-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_product_support
-- name    : OAI.PiExponent.FormalInterpolation.bounded_product_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:39:48.823432+00:00
-- url     : https://prove2.me/theorems/6adbb622-7b3a-4d83-af5e-addbee09a715
-- title:
--   Support bound for a product of coordinate representatives
-- statement:
--   If each factor is supported only in its own coordinate and its exponent there is below `N`, every exponent in the product has every coordinate below `N`.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_product_support
    {m : Nat}
    (N : Nat)
    (R : Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex)
    (hR : ∀ i : Fin (m + 1), ∀ b ∈ (R i).support,
      b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) :
    ∀ b ∈ (∏ i : Fin (m + 1), R i).support,
      ∀ i : Fin (m + 1), b i < N := by sorry
