-- Prove2me | Theorems.Thm_KKBinPacking_LinearGrouping_instLE_monotone
-- name    : KKBinPacking.LinearGrouping.instLE_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:21:18.179081+00:00
-- url     : https://prove2.me/theorems/d19d6518-c730-46e9-af18-5ed4cce51271
-- title:
--   $I \le J$ implies $OPT(I) \le OPT(J)$, $LIN(I) \le LIN(J)$, $SIZE(I) \le SIZE(J)$
-- statement:
--   Let $I$ and $J$ be instances with $I \le J$, i.e. there is a one-to-one map $f$ from the pieces of $I$ into the pieces of $J$ such that every piece $x$ of $I$ is no larger than $f(x)$. Then
--
--   $$
--   OPT(I) \le OPT(J), \qquad LIN(I) \le LIN(J), \qquad SIZE(I) \le SIZE(J).
--   $$
--
--   This monotonicity is what makes rounding sizes up (linear grouping) a safe relaxation.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 314, §4 Linear Grouping, unlabelled display after the definition of the order I ≤ J (right column, top)

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared

namespace KKBinPacking.LinearGrouping
theorem instLE_monotone (I J : Multiset ℝ) (hI : IsInstance I) (hJ : IsInstance J)
    (hIJ : InstLE I J) :
    OPT I ≤ OPT J ∧ LIN I ≤ LIN J ∧ SIZE I ≤ SIZE J := by sorry
end KKBinPacking.LinearGrouping
