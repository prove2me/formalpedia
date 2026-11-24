-- Prove2me | Theorems.Thm_LefebvreVariations_oppermann_of_le_300
-- name    : LefebvreVariations.oppermann_of_le_300
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:41:27.721811+00:00
-- url     : https://prove2.me/theorems/ed2a77e6-a62d-4e39-adee-200cef738c62
-- title:
--   Lefebvre's variations: Oppermann's conjecture for $n\le 300$
-- statement:
--   This verifies Oppermann's conjecture for $2\le n\le300$.
--
--   For every integer $n$ with $2\le n\le300$ there is a prime $p$ with $n^2-n<p<n^2$ and a prime $q$ with $n^2<q<n^2+n$.
--
--   Oppermann's conjecture (1882) asserts this for every $n\ge2$; it implies Legendre's conjecture (a prime between consecutive squares) and Brocard's conjecture, and remains open. Here an explicit pair of primes is given for each of the $299$ values of $n$ and each primality is certified.
--
--   **Formalization Note** The statement is the parent's at each $n\le300$; witnesses are the largest prime below $n^2$ and the smallest prime above $n^2$.
-- source:
--   L. Oppermann, Om vor Kundskab om Primtallenes Mængde mellem givne Grændser, Oversigt over det Kongelige Danske Videnskabernes Selskabs Forhandlinger (1882), 169–179 (the conjecture); the range 2 ≤ n ≤ 300 is an explicit finite verification. Parent problem: OppermannConjecture.oppermann.

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Set.Basic

open Set

namespace LefebvreVariations

/-- **Oppermann's conjecture for `2 ≤ n ≤ 300`**: a prime in `(n² − n, n²)` and one in
`(n², n² + n)`, by a finite check up to `90300`. Oppermann (1882); the unconditional state of the art
is Baker–Harman–Pintz, *The difference between consecutive primes, II*, Proc. London Math. Soc.
83 (2001) 532–562, which gives a prime in `[x, x + x^{0.525}]` only. -/
theorem oppermann_of_le_300 (n : ℕ) (h : n > 1) (hn : n ≤ 300) :
    (∃ p : ℕ, Nat.Prime p ∧ p ∈ Ioo (n ^ 2 - n) (n ^ 2)) ∧
    (∃ q : ℕ, Nat.Prime q ∧ q ∈ Ioo (n ^ 2) (n ^ 2 + n)) := by
  sorry

end LefebvreVariations
