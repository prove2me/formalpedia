-- Prove2me | Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_lin_telescoping
-- name    : KKBinPacking.GeometricGrouping.alg2_lin_telescoping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T17:35:22.758669+00:00
-- url     : https://prove2.me/theorems/4079cd64-9798-4e48-b350-081a6098de00
-- title:
--   Analysis of ALGORITHM 2 — $LIN(I_{i+1}) \le LIN(J_i) + 1 - X_i \le LIN(I_i) + 1 - X_i$, hence $\sum_i X_i \le LIN(J_1) + t$
-- statement:
--   Consider any run of ALGORITHM 2 with an integer parameter $k \ge 2$ and a real parameter $g > 0$ on an instance $I$, whose while loop is executed $t$ times. For the $i$-th execution let $I_i$ be the instance at its beginning, $J_i$ the rounded instance produced by geometric grouping, and $X_i = \sum_{x_j \ge 1}\lfloor x_j\rfloor$ the number of bins created from the basic feasible solution $x$ of the linear program of $J_i$. Then for every execution
--
--   $$LIN(I_{i+1}) \le LIN(J_i) + 1 - X_i \le LIN(I_i) + 1 - X_i,$$
--
--   and summing over the executions,
--
--   $$\sum_{i=1}^{t} X_i \le LIN(J_1) + t .$$
--
--   The bins created from the linear programming solutions therefore cost at most one more than the fractional optimum per iteration.
--
--   **Formalization Note** Executions are numbered $0,\dots,t-1$ in Lean, so the paper's $LIN(J)$, i.e. $LIN(J_1)$, is `LIN (geomJ k (tr.inst 0))`, the value for the rounded instance of the first execution. For $t = 0$ the sum is empty and the bound holds because $LIN \ge 0$.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 316, Analysis of ALGORITHM 2, last display of the right column

import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem alg2_lin_telescoping (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) :
    (∀ i < tr.t,
      LIN (tr.inst (i + 1)) ≤ LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ∧
        LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ≤
          LIN (tr.inst i) + 1 - principalCount (tr.x i)) ∧
    ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) ≤
      LIN (geomJ k (tr.inst 0)) + tr.t := by sorry
end KKBinPacking.GeometricGrouping
