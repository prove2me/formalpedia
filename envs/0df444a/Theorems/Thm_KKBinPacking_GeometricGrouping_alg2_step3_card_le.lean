-- Prove2me | Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_step3_card_le
-- name    : KKBinPacking.GeometricGrouping.alg2_step3_card_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T17:39:03.907315+00:00
-- url     : https://prove2.me/theorems/641936bb-5a63-4aa2-9352-d96c0186cb3f
-- title:
--   Analysis of ALGORITHM 2 — the packing after Step 3 has at most $\sum_i X_i + t[2k(2+\ln\frac1g)] + 2 + \frac{2}{1-1/k}\ln\frac1g$ bins
-- statement:
--   Consider any run of ALGORITHM 2 with an integer parameter $k \ge 2$ and a real parameter $g > 0$ on an instance $I$, whose while loop is executed $t$ times, and let $X_i$ be the number of bins created from the linear programming solution in the $i$-th execution. The bins produced up to the end of Step 3 (the bins created from the solutions, the bins packing the instances $J'_i$, and the Step 3 bins) form a packing of the pieces of $I$ of size $> g$, and their number is at most
--
--   $$\sum_{i=1}^{t} X_i + t\Bigl[2k\Bigl(2 + \ln\frac1g\Bigr)\Bigr] + 2 + \frac{2}{1-\frac1k}\ln\frac1g .$$
--
--   This is the cost of the packing before the small pieces are reinserted.
--
--   **Formalization Note** The packing property (every bin has load at most $1$ and the bins hold exactly the pieces of size $> g$) is stated together with the count; it holds because every real piece placed in a principal bin is no larger than the rounded size it replaces.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 317, "The number of bins in the packing produced after Step 3 is" (left column, first display)

import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem alg2_step3_card_le (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) :
    IsPacking (I.filter (fun p => g < p)) (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) ∧
    (Multiset.card (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) : ℝ) ≤
      ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) +
        tr.t * (2 * (k : ℝ) * (2 + Real.log (1 / g))) +
        2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g) := by sorry
end KKBinPacking.GeometricGrouping
