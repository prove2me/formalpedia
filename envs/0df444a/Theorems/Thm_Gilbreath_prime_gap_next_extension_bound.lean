-- Prove2me | Theorems.Thm_Gilbreath_prime_gap_next_extension_bound
-- name    : Gilbreath.prime_gap_next_extension_bound
-- status  : Open
-- author  : @EvanLLL
-- created : 2026-09-26T00:12:04.765077+00:00
-- url     : https://prove2.me/theorems/70daca94-9c8d-47ed-a38a-2aad79c728de
-- title:
--   The next normalized prime gap lies within the boundary bound
-- statement:
--   Let $p_0=2<p_1=3<\cdots$ be the increasing primes and let $b_n=(p_{n+2}-p_{n+1})/2$. Write $T_j=(\Delta^j b)(0)$, where $\Delta$ takes adjacent absolute differences. For $n\ge1$, let
--   $$
--   E_n=(b_{n-1},(\Delta b)(n-2),\ldots,(\Delta^{n-1}b)(0))
--   $$
--   be the ordered right boundary of the first $n$ normalized gaps, and put $E_0=()$.
--
--   Assume the shorter prefix has binary leading entries:
--   $$
--   T_j\le1\qquad(0\le j<n).
--   $$
--
--   The assertion is the size bound
--   $$
--   b_n\le1+\sum_{e\in E_n}e.
--   $$
--
--   This is a new open estimate for actual prime gaps under the finite-prefix hypothesis. Paired with ordered completeness of the same boundary, it would show that the next input produces a binary bottom entry. Both conditions refer to this uniquely determined boundary; no auxiliary parameters are chosen independently. The estimate is not claimed to follow from the cited paper.
-- source:
--   L. Muney, Holes in Valid-Extension Sets of Finite Gilbreath Sequences, arXiv:2606.23721v1, https://arxiv.org/html/2606.23721v1, Section 2, Corollary 3 (candidate bound), and Section 9, Theorem 20 (normalized candidate interval). The displayed conditional estimate for the next actual prime gap is an open assertion proposed for this decomposition, not a theorem of the cited paper.

import Definitions.Def_gilbreath_finite_extension

namespace Gilbreath
theorem prime_gap_next_extension_bound (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (n : ℕ)
    (hprefix : ∀ j, j < n → iterAbsDiff b j 0 ≤ 1) :
    b n ≤ (extensionBoundary b n).sum + 1 := by sorry
end Gilbreath
