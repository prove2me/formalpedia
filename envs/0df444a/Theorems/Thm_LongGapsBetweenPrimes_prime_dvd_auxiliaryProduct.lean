-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_prime_dvd_auxiliaryProduct
-- name    : LongGapsBetweenPrimes.prime_dvd_auxiliaryProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:36.940577+00:00
-- url     : https://prove2.me/theorems/87a2b590-5af9-419b-9496-b04403347cc3
-- title:
--   Long Gaps Between Primes: prime dvd auxiliary Product
-- statement:
--   Every prime divisor of the auxiliary product is an auxiliary prime.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1567-L1570
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1567-L1570

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.prime_dvd_auxiliaryProduct {Z Y p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ auxiliaryProduct Z Y) : p ∈ auxiliaryPrimes Z Y := by sorry
