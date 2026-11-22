-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_exists_linear_roots
-- name    : LongGapsBetweenPrimes.exists_linear_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:03.791701+00:00
-- url     : https://prove2.me/theorems/7c4fa894-45ea-4e78-bf47-d298089b9217
-- title:
--   Long Gaps Between Primes: exists linear roots
-- statement:
--   Construct distinct modular roots forcing divisibility of the translated linear forms.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3584-L3609
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3584-L3609

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.exists_linear_roots {p k Q b : ℕ} (hp : p.Prime) (hQ : Q.Coprime p)
    (s : Fin k → ℕ) (hs : Function.Injective s) (hsmall : ∀ i, s i < p) :
    ∃ root : Fin k → Fin p, Function.Injective root ∧
      ∀ n i, n % p = (root i).val → p ∣ b + Q * (n + 1) + s i := by sorry
