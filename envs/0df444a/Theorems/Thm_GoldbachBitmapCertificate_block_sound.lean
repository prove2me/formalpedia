-- Prove2me | Theorems.Thm_GoldbachBitmapCertificate_block_sound
-- name    : GoldbachBitmapCertificate.block_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T01:01:41.063187+00:00
-- url     : https://prove2.me/theorems/38941c8d-e66d-46d5-a83d-c01e6068d5a4
-- title:
--   Soundness of complete interval coverage by shifted prime bitmaps
-- statement:
--   Let a checked prime dictionary, a checked list of odd left primes within a bound,
--   and a shifted-prime bitmap cover a contiguous interval of half-indices. Then
--   every even number in the corresponding interval is the sum of two primes, with
--   the left summand within the bound.
--
--   The proof proceeds by the semantics of individual bits. Structural induction on
--   the dictionary shows that each set bit represents an actual odd prime with the
--   stated half-index. Induction on the left-prime list shows that each covered bit
--   comes from a shift by a checked odd prime. The interval-mask identity forces
--   every target bit to be set, not merely a sample or a subset of the interval.
--   The odd-prime half-sum identity then recovers the original even number.
--
--   The origin guards rule out false bits from truncated subtraction, and primality
--   of every dictionary node is established by the integer-square-root checker.
--   No ordering property of the dictionary is assumed for soundness. The theorem is
--   generic and supplies a certificate-checking method; a concrete finite bound
--   requires concrete data passing all checks. It does not prove strong Goldbach.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Definitions.Def_GoldbachBitmapCertificate
import Mathlib.Algebra.Ring.Parity
set_option autoImplicit false

theorem GoldbachBitmapCertificate.block_sound (base first count smallBound : ℕ) (tree : GoldbachCertificate.PrimeTree)
    (left : List ℕ) (ht : tree.check = true)
    (hl : GoldbachBitmapCertificate.leftCheck smallBound tree left = true)
    (hc : GoldbachBitmapCertificate.covers base first count tree left = true)
    (n : ℕ) (hlo : 2 * (base + first) ≤ n)
    (hhi : n < 2 * (base + first + count)) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by sorry
