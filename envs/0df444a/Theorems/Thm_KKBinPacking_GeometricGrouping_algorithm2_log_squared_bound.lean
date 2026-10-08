-- Prove2me | Theorems.Thm_KKBinPacking_GeometricGrouping_algorithm2_log_squared_bound
-- name    : KKBinPacking.GeometricGrouping.algorithm2_log_squared_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T17:49:20.89798+00:00
-- url     : https://prove2.me/theorems/481bbaf2-8553-4e36-9fed-66bb54f00da2
-- title:
--   Theorem 4 — ALGORITHM 2 with $k=2$, $g = 1/SIZE(I)$ packs within $OPT(I) + O(\log^2 OPT(I))$ bins
-- statement:
--   Let $I$ be an instance of the one-dimensional bin-packing problem with $SIZE(I) \ge 2$, and run ALGORITHM 2 with parameters $k = 2$ and $g = 1/SIZE(I)$. Every packing $P$ it can output is a packing of $I$, and its number of bins $A(I) = |P|$ satisfies
--
--   $$A(I) \le OPT(I) + \bigl(1 + \log_2 OPT(I)\bigr)\bigl(9 + 4\ln OPT(I)\bigr) + 2 + 4\ln OPT(I).$$
--
--   In particular $A(I) \le OPT(I) + O(\log^2 OPT(I))$: the additive error of this algorithm grows only polylogarithmically in the optimum.
--
--   **Formalization Note** The paper writes $A(I) \le OPT(I) + O(\log^2 OPT(I))$; its proof, the general bound for ALGORITHM 2 with $k = 2$ and $g = 1/SIZE(I)$ together with $SIZE(I) \le OPT(I)$ (Lemma 2) and $OPT(I) \le 2\,SIZE(I)+1$ (Lemma 1), yields the explicit constants stated here. The hypothesis $SIZE(I) \ge 2$ makes the paper's asymptotic threshold explicit: Lemma 3 is applied with parameter $2g = 2/SIZE(I)$, which must be at most $1$, and for $SIZE(I) < e^{-1/2}$ the while loop of ALGORITHM 2 with $g = 1/SIZE(I)$ never terminates. The bound holds for every run of the algorithm (every output of the Fractional Bin-Packing subroutine within its contract, every admissible packing at Steps 2 and 3, every run of the Step 4 insertion). The statements about running time and the number of subroutine calls are not formalized. Logarithms: $\ln$ is `Real.log`, $\log_2$ is `Real.logb 2`.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 317, Theorem 4 (left column), with the display "Hence by Lemma 3" at k = 2, g = 1/SIZE(I)

import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem algorithm2_log_squared_bound (I : Multiset ℝ) (hI : IsInstance I) (hS : 2 ≤ SIZE I)
    (P : Multiset (Multiset ℝ)) (hP : Alg2Run 2 (1 / SIZE I) I P) :
    IsPacking I P ∧
      (Multiset.card P : ℝ) ≤
        (OPT I : ℝ) + (1 + Real.logb 2 (OPT I)) * (9 + 4 * Real.log (OPT I)) +
          2 + 4 * Real.log (OPT I) := by sorry
end KKBinPacking.GeometricGrouping
