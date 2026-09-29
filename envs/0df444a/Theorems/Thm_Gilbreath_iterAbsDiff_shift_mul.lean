-- Prove2me | Theorems.Thm_Gilbreath_iterAbsDiff_shift_mul
-- name    : Gilbreath.iterAbsDiff_shift_mul
-- status  : Proved
-- author  : @EvanLLL
-- created : 2026-09-25T14:07:21.247533+00:00
-- url     : https://prove2.me/theorems/8adb9bc6-653e-48a5-ad0b-dd414a6ef8c8
-- title:
--   Shift and scaling covariance of iterated absolute differences
-- statement:
--   For a sequence $a:\mathbb N\to\mathbb N$, write $(\Delta a)(n)=|a(n+1)-a(n)|$ and let $\Delta^k$ denote its $k$-fold iterate. Let $c,s,k,n$ be arbitrary nonnegative integers, and put $\widetilde a(j)=c\,a(j+s)$. Then
--   $$
--   (\Delta^k\widetilde a)(n)=c\,(\Delta^k a)(n+s).
--   $$
--
--   The identity includes $c=0$, $k=0$, and $s=0$. It expresses compatibility of the entire difference triangle with restriction to a tail and multiplication by a nonnegative integer. In particular, it transfers statements about the halved prime-gap triangle to the even tail of the Gilbreath triangle.
-- source:
--   Structural consequence of the recurrence defining absDiff and iterAbsDiff in Definitions.Def_gilbreath_triangle, https://prove2.me/theorems/54d54393-a9a5-4c00-b9f5-108b4f94026c. The one-step identity is |c x-c y|=c|x-y| for c>=0; the asserted iterated identity is the derived lemma formalized here.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem iterAbsDiff_shift_mul (a : ℕ → ℕ) (c s k n : ℕ) :
    iterAbsDiff (fun j => c * a (j + s)) k n =
      c * iterAbsDiff a k (n + s) := by sorry
end Gilbreath
