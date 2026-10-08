-- Prove2me | Theorems.Thm_GoldbachBitmapCertificate_even_4_65536
-- name    : GoldbachBitmapCertificate.even_4_65536
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T01:01:52.026004+00:00
-- url     : https://prove2.me/theorems/ed604577-2836-4547-93d0-9cf4baf7b95e
-- title:
--   A compressed checked Goldbach certificate through 65536
-- statement:
--   Every even integer from 4 through 65,536 is the sum of two primes, with the left
--   summand at most 5,569. The certificate proves primality of a dictionary of 6,542
--   distinct primes and checks a list of 45 odd left primes. Those left primes are
--   in fact all at most 293. The even number 4 is handled separately as 2 + 2.
--
--   For all remaining targets, bitwise union of shifted odd-prime bitmaps covers
--   every half-index from 3 through 32,768. The interval mask has 32,766 target bits.
--   The generic soundness argument proves that each target bit yields an actual
--   prime pair; no generated witnesses or Python primality answers are trusted.
--   The source embeds its closed soundness proof so it has no open theorem
--   dependency. Lean checks the concrete Boolean equalities in its kernel, without
--   `native_decide`.
--
--   The local replay passed in approximately 91 seconds on a shared machine, with
--   only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The
--   source is 141,889 bytes. This is a bounded test of certificate compression, not
--   a new analytic Goldbach result, and not certification of the much larger
--   `4·10^14` or `4·10^18` ranges used elsewhere on the platform.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Definitions.Def_GoldbachBitmapCertificate
import Mathlib.Algebra.Ring.Parity
set_option autoImplicit false

theorem GoldbachBitmapCertificate.even_4_65536 (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 65536)
    (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 5569 ∧ n = p + q := by sorry
