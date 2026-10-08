-- Prove2me | Theorems.Thm_GoldbachCertificate_block_sound
-- name    : GoldbachCertificate.block_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T00:33:10.536486+00:00
-- url     : https://prove2.me/theorems/68deb882-f59d-4f1e-beba-5dc18218b332
-- title:
--   Soundness of consecutive even Goldbach certificates
-- statement:
--   Let $T$ be a finite prime dictionary, $a,s$ natural numbers, and $L$ an ordered list of prime-pair candidates. If the dictionary primality check succeeds and every row check succeeds, then every even natural number
--
--   $$2a\le n<2(a+|L|)$$
--
--   has a representation $n=p+q$ with both $p$ and $q$ prime and $p\le s$.
--
--   The proof establishes the primality test by the square-root divisor criterion, proves soundness of dictionary lookup by structural induction, and then proves coverage of the entire even interval by induction on the row list. The half-open endpoint depends on the exact list length: a missing row cannot certify an extra case. Equal primes are allowed, including $4=2+2$.
--
--   This is a reusable computational-certificate soundness theorem. It assumes successful checks, not Goldbach or any prime-distribution estimate. All proof dependencies are standard Lean foundations. It is not a claim of a new result about the infinite Goldbach problem.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Definitions.Def_GoldbachCertificate
import Mathlib.Algebra.Ring.Parity
set_option autoImplicit false

theorem GoldbachCertificate.block_sound (first smallBound : ℕ) (tree : GoldbachCertificate.PrimeTree)
    (rows : List (ℕ × ℕ)) (ht : tree.check = true)
    (hr : GoldbachCertificate.checkRows first smallBound tree rows = true)
    (n : ℕ) (hlo : 2 * first ≤ n) (hhi : n < 2 * (first + rows.length))
    (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by sorry
