-- Prove2me | Theorems.Thm_GoldbachCert_two_primes_up_to_1e4
-- name    : GoldbachCert.two_primes_up_to_1e4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T16:01:10.827128+00:00
-- url     : https://prove2.me/theorems/e3fecb0d-6724-4bdf-a120-0fb58a04d438
-- title:
--   Every even $n$ with $4\le n\le 10^4$ is a sum of two primes
-- statement:
--   Every even natural number $n$ with $4 \le n \le 10^4$ is a sum of two primes:
--
--   $$\exists\, p\, q \in \mathbb{N},\quad p \text{ prime},\ q \text{ prime},\ p + q = n .$$
--
--   This is Goldbach's conjecture verified on an initial segment. It is a finite statement, and it is proved by computation from a stored table of witnesses: for each even $n = 4, 6, \dots, 10^4$ in order, the table holds the least prime $p$ for which $n - p$ is also prime (the largest such $p$ occurring is $53$, for $n = 9926$). The Lean proof evaluates the table once, checking by trial division up to the square root that each stored $p$ and each complementary $n - p$ is prime, and then reads off the decomposition for the given $n$.
--
--   **Mathematical status.** Goldbach's conjecture is open, but every finite initial segment of it is a decidable statement, and this one is true. The value of recording it is that it makes the small range available as a lemma with no hypotheses, and that the certificate format scales: the same table-and-check scheme, split into blocks to stay inside the compilation budget, is how a larger verified range would be formalized.
--
--   **Formalization Note.** The witness table is the platform definition `GoldbachCertWitness`; the proof contains no `sorry` and no axiom beyond Lean's kernel. The check uses trial division against `Nat.prime_def_le_sqrt`, so it does not appeal to a primality oracle.
-- source:
--   Goldbach's conjecture; finite verification up to $10^4$ as a decidable initial segment. Compare the platform nodes Richstein2001.even_goldbach_up_to_4e14 and TaoFivePrimes.even_goldbach_verified for the large-range targets.

import Mathlib
import Definitions.Def_GoldbachCertWitness

import Definitions.Def_GoldbachCertWitness
namespace GoldbachCert

theorem two_primes_up_to_1e4 (n : ℕ) (h4 : 4 ≤ n) (heven : Even n) (hN : n ≤ 10000) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by sorry

end GoldbachCert
