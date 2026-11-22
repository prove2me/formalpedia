-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_productKernel_diag
-- name    : LongGapsBetweenPrimes.productKernel_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:46.441797+00:00
-- url     : https://prove2.me/theorems/9f74f027-1c94-4857-99ad-68a89a35fd9a
-- title:
--   Long Gaps Between Primes: product Kernel diag
-- statement:
--   The product Gram kernel has diagonal entries equal to one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L615-L617
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L615-L617

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.productKernel_diag {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : productKernel size σ σ = 1 := by sorry
