-- Prove2me | Theorems.Thm_GoldbachCertificate_even_4_16384
-- name    : GoldbachCertificate.even_4_16384
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T00:33:30.674978+00:00
-- url     : https://prove2.me/theorems/c9c91f42-3162-4d74-b6a6-a095aa5ba74c
-- title:
--   A replayed Goldbach certificate for every even number from 4 through 16384
-- statement:
--   Every even natural number $n$ with $4\le n\le16384$ has a representation $n=p+q$ by two primes, with $p\le5569$.
--
--   The proof replays a literal certificate containing 8,191 consecutive pairs and a shared dictionary of 1,900 prime values. It checks primality, dictionary membership, every exact sum and the left-prime bound. Coverage follows from the proved certificate checker and the exact row count; it is not sampling. The submitted proof contains its own soundness argument, so it does not assume an Open checker theorem.
--
--   This is a reproducibility and performance pilot for formal finite Goldbach verification. The numerical range is long known and is far smaller than the $4\cdot10^{14}$ finite input used in Tao's five-primes argument. This certificate does not discharge that full input or establish strong Goldbach. Larger scale requires independently verified complete coverage and a credible measured checking cost.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Definitions.Def_GoldbachCertificate
import Mathlib.Algebra.Ring.Parity
set_option autoImplicit false

theorem GoldbachCertificate.even_4_16384 (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 16384)
    (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 5569 ∧ n = p + q := by sorry
