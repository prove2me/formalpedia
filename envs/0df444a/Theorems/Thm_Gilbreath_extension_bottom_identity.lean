-- Prove2me | Theorems.Thm_Gilbreath_extension_bottom_identity
-- name    : Gilbreath.extension_bottom_identity
-- status  : Proved
-- author  : @EvanLLL
-- created : 2026-09-26T00:12:11.749952+00:00
-- url     : https://prove2.me/theorems/89f7f204-4de7-4272-acc4-5c5cdddf231f
-- title:
--   The new bottom entry is the ordered boundary fold
-- statement:
--   Let $a:\mathbb N\to\mathbb N$ and let $E_a(n)$ be the ordered right boundary of the triangle on $a_0,\ldots,a_{n-1}$, read from the top row downwards; $E_a(0)$ is empty. For a tuple $E=(e_0,\ldots,e_{n-1})$, let $F_E(x)$ successively replace $x$ by $|x-e_i|$ in this order. Then
--   $$
--   F_{E_a(n)}(a_n)=(\Delta^n a)(0).
--   $$
--
--   This identifies the new bottom entry created by appending the next input. It is valid for arbitrary natural-valued inputs, including $n=0$, without a primality or previous-leading-entry assumption.
-- source:
--   L. Muney, Holes in Valid-Extension Sets of Finite Gilbreath Sequences, arXiv:2606.23721v1, https://arxiv.org/html/2606.23721v1, Section 2, Proposition 2 and its right-edge recurrence. This is the underlying bottom-entry identity, stated for zero-based natural-valued sequences and including the top-row boundary entry.

import Definitions.Def_gilbreath_finite_extension

namespace Gilbreath
theorem extension_bottom_identity (a : ℕ → ℕ) (n : ℕ) :
    extensionFold (extensionBoundary a n) (a n) = iterAbsDiff a n 0 := by sorry
end Gilbreath
