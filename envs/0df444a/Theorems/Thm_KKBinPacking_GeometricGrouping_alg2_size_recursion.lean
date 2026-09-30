-- Prove2me | Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_size_recursion
-- name    : KKBinPacking.GeometricGrouping.alg2_size_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T17:30:04.605163+00:00
-- url     : https://prove2.me/theorems/a124aa6e-2251-4a70-9b82-2dd8cdbd4934
-- title:
--   Analysis of ALGORITHM 2 — $SIZE(I_{i+1}) \le LIN(I_{i+1}) \le \sum_j (x_j - \lfloor x_j\rfloor) \le m(J_i)$ and $SIZE(I_{i+1}) \le SIZE(I_i)/k + \ln(1/g)$
-- statement:
--   Consider any run of ALGORITHM 2 with an integer parameter $k \ge 2$ and a real parameter $0 < g \le 1$ on an instance $I$. For an execution $i$ of the body of the while loop, let $I_i$ be the instance at its beginning, $J_i$ the rounded instance produced by geometric grouping of $I_i$, $x$ the basic feasible solution obtained for the linear program of $J_i$, and $I_{i+1}$ the instance at the beginning of the next execution. Then
--
--   $$SIZE(I_{i+1}) \le LIN(I_{i+1}) \le \sum_j \bigl(x_j - \lfloor x_j\rfloor\bigr) \le m(J_i) \le \frac{SIZE(I_i)}{k} + \ln\frac1g,$$
--
--   and in particular
--
--   $$SIZE(I_{i+1}) \le \frac{SIZE(I_i)}{k} + \ln\frac1g .$$
--
--   The total size of the instance thus shrinks geometrically from one iteration to the next, which bounds the number of iterations.
--
--   **Formalization Note** The sum runs over the support of $x$. The paper's chain passes through $m(J_i) \le SIZE(J_i)/k + \ln(1/g)$, an instance of Theorem 2, item 4, which is false as printed (see the corrected item 4); the link $m(J_i) \le SIZE(I_i)/k + \ln(1/g)$ stated here holds because all groups but the last are full. Executions are numbered from $0$ in Lean (`tr.inst i` is the instance at the beginning of execution $i$), and the statement holds for every execution $i < t$ of every trace.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 316, Analysis of ALGORITHM 2, first display after "We first derive an upper bound on t" (right column)

import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem alg2_size_recursion (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t) :
    SIZE (tr.inst (i + 1)) ≤ LIN (tr.inst (i + 1)) ∧
      LIN (tr.inst (i + 1)) ≤ ∑ c ∈ (tr.x i).support, (tr.x i c - (⌊tr.x i c⌋₊ : ℝ)) ∧
      ∑ c ∈ (tr.x i).support, (tr.x i c - (⌊tr.x i c⌋₊ : ℝ)) ≤ numSizes (geomJ k (tr.inst i)) ∧
      (numSizes (geomJ k (tr.inst i)) : ℝ) ≤ SIZE (tr.inst i) / k + Real.log (1 / g) ∧
      SIZE (tr.inst (i + 1)) ≤ SIZE (tr.inst i) / k + Real.log (1 / g) := by sorry
end KKBinPacking.GeometricGrouping
