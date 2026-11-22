-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_productKernel_symm
-- name    : LongGapsBetweenPrimes.productKernel_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:45.165799+00:00
-- url     : https://prove2.me/theorems/c10fb695-94b1-493c-9b92-8cd35161a3e4
-- title:
--   Long Gaps Between Primes: product Kernel symm
-- statement:
--   The product Gram kernel is symmetric.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L610-L612
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L610-L612

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.productKernel_symm {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ τ : α → Option (Fin k)) : productKernel size σ τ = productKernel size τ σ := by sorry
