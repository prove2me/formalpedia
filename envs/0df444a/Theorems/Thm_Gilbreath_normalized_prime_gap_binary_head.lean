-- Prove2me | Theorems.Thm_Gilbreath_normalized_prime_gap_binary_head
-- name    : Gilbreath.normalized_prime_gap_binary_head
-- status  : Open
-- author  : @EvanLLL
-- created : 2026-09-25T14:07:31.14184+00:00
-- url     : https://prove2.me/theorems/4684c97d-b01a-42f2-b613-7a8f0a362a2b
-- title:
--   Binary leading entries in the normalized prime-gap triangle
-- statement:
--   Let $p_0=2<p_1=3<\cdots$ be the increasing primes. Suppose that the sequence $b:\mathbb N\to\mathbb N$ satisfies
--   $$
--   2b_n=p_{n+2}-p_{n+1}\quad(n\ge0).
--   $$
--   For the absolute-difference operator $(\Delta a)(n)=|a(n+1)-a(n)|$, the assertion is
--   $$
--   (\Delta^k b)(0)\in\{0,1\}\qquad(k\ge0).
--   $$
--
--   This is the remaining open arithmetic assertion in the normalized prime-gap reformulation of Gilbreath's conjecture. The normalization exists and is unique. Shift and scaling covariance identify twice the displayed entry with $d^{k+1}(1)$, so the assertion is equivalent to the second-column formulation and to the original zero-two-block target. No claim is made that this assertion follows merely from positivity or integrality of $b$.
-- source:
--   Equivalent normalized restatement of Gilbreath.zero_two_blocks, https://prove2.me/theorems/4e6e2458-bb2f-4e27-83b7-f950275a4e4b, natural-language discussion of halved prime gaps and the case k=K+1,m=0; also Gilbreath.second_column, https://prove2.me/theorems/9b122789-850c-40e4-9ea8-39ab4c7a29b7. This remains an open conjecture.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem normalized_prime_gap_binary_head (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (k : ℕ) :
    iterAbsDiff b k 0 = 0 ∨ iterAbsDiff b k 0 = 1 := by sorry
end Gilbreath
