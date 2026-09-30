-- Prove2me | Theorems.Thm_KKBinPacking_LinearGrouping_opt_le_two_size_add_one
-- name    : KKBinPacking.LinearGrouping.opt_le_two_size_add_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T11:19:13.860911+00:00
-- url     : https://prove2.me/theorems/6170d854-e4a2-4bc8-91f6-fb208b94d546
-- title:
--   Lemma 1 — $OPT(I) \le 2\,SIZE(I) + 1$
-- statement:
--   Let $I$ be an instance of the one-dimensional bin-packing problem, with $OPT(I)$ the minimum number of bins in a packing of $I$ and $SIZE(I)$ the total size of its pieces. Then
--
--   $$
--   OPT(I) \le 2\,SIZE(I) + 1 .
--   $$
--
--   This crude bound is used to pack the residual instance in the rounding argument of Lemma 2 and Corollary 1.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 313, Lemma 1

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance

namespace KKBinPacking.LinearGrouping
theorem opt_le_two_size_add_one (I : Multiset ℝ) (hI : IsInstance I) :
    (OPT I : ℝ) ≤ 2 * SIZE I + 1 := by sorry
end KKBinPacking.LinearGrouping
