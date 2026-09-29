-- Prove2me | Theorems.Thm_Gilbreath_prime_gap_ordered_extension_condition
-- name    : Gilbreath.prime_gap_ordered_extension_condition
-- status  : Open
-- author  : @EvanLLL
-- created : 2026-09-26T00:12:16.920321+00:00
-- url     : https://prove2.me/theorems/093a11b2-5457-4307-a5ef-5c071bf28a3e
-- title:
--   Ordered boundary completeness for a binary prime-gap prefix
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
--   The assertion is that, writing $E_n=(e_0,\ldots,e_{n-1})$,
--   $$
--   e_i\le1+\sum_{r>i}e_r\qquad(0\le i<n).
--   $$
--
--   This is a new open, prime-specific sufficient-condition conjecture for the finite-extension route. Together with a bound placing the next normalized gap inside the candidate interval, it would provide the induction step. The hypothesis concerns only indices strictly below $n$. The assertion is not claimed for arbitrary positive input sequences, and it is not established by the cited finite-extension theorem.
-- source:
--   L. Muney, Holes in Valid-Extension Sets of Finite Gilbreath Sequences, arXiv:2606.23721v1, https://arxiv.org/html/2606.23721v1, Section 9, Theorem 20, supplies the general ordered-completeness predicate. The assertion that normalized actual-prime prefixes satisfy this predicate under the displayed finite-prefix hypothesis is a new open conjecture formulated for this decomposition; it is not a result stated or proved in that paper.

import Definitions.Def_gilbreath_finite_extension

namespace Gilbreath
theorem prime_gap_ordered_extension_condition (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (n : ℕ)
    (hprefix : ∀ j, j < n → iterAbsDiff b j 0 ≤ 1) :
    ExtensionComplete (extensionBoundary b n) := by sorry
end Gilbreath
