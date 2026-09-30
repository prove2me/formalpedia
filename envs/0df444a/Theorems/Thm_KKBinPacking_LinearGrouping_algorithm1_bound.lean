-- Prove2me | Theorems.Thm_KKBinPacking_LinearGrouping_algorithm1_bound
-- name    : KKBinPacking.LinearGrouping.algorithm1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:25:20.998358+00:00
-- url     : https://prove2.me/theorems/63279ce1-5d42-4f8e-af48-4f268f1f8ef0
-- title:
--   Theorem 3, corrected — ALGORITHM 1 packs within $(1+2\varepsilon)OPT(I) + 1/(2\varepsilon^2) + 3$ bins
-- statement:
--   Let $\varepsilon > 0$ and let $I$ be an instance of the one-dimensional bin-packing problem (finitely many pieces with sizes in $(0,1)$). Let $P$ be any packing that ALGORITHM 1 with parameter $\varepsilon$ may output on $I$, and write $A(I)$ for its number of bins. Then $P$ is a packing of $I$ and
--
--   $$
--   A(I) \le (1 + 2\varepsilon)\,OPT(I) + \frac{1}{2\varepsilon^2} + 3 .
--   $$
--
--   Since the additive term does not depend on $I$, ALGORITHM 1 is an asymptotic approximation scheme: its asymptotic worst-case ratio is at most $1 + 2\varepsilon$ for every $\varepsilon > 0$.
--
--   **Formalization Note** The paper prints $A(I) \le (1+\varepsilon)\,OPT(I) + 1/(2\varepsilon^2) + 3$, which is false for ALGORITHM 1 as printed. For $\varepsilon = 1/10$ and $I$ consisting of $19\,000$ pieces of size $0.051$: nothing is discarded, $k = 190$, the $190$ largest pieces take $190$ bins in Step 3, and $K$ consists of $18\,810$ pieces of size $0.051$, which need at least $\lceil 18\,810/19\rceil = 990$ bins; a run with $990$ bins in Step 5 exists ($x = 990$ on the configuration of $19$ pieces is basic and optimal). So some run outputs $1180$ bins, while $OPT(I) = 1000$ and $(1+\varepsilon)\,OPT(I) + 1/(2\varepsilon^2) + 3 = 1153$. The failing step is (ii) of the proof, which uses $SIZE(J) \ge \varepsilon\, n(J)$ although Step 1 only discards pieces of size $\le \varepsilon/2$. The statement here is the paper's proof with that step corrected ($SIZE(J) \ge (\varepsilon/2)\,n(J)$). Running ALGORITHM 1 with $\varepsilon/2$ recovers the paper's result (4), $A(I) \le (1+\varepsilon)\,OPT(I) + O(\varepsilon^{-2})$. The bound is stated for every $\varepsilon > 0$ and every run (every admissible output of the Fractional Bin-Packing subroutine and every choice in Steps 5–7). The running-time half of Theorem 3 is not stated.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 316, Theorem 3 (left column), approximation bound, corrected (printed bound (1 + ε) OPT(I) + 1/(2ε²) + 3 fails)

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_LinearGrouping_LinGroup
import Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
open KKBinPacking.Shared

namespace KKBinPacking.LinearGrouping
theorem algorithm1_bound (ε : ℝ) (hε : 0 < ε) (I : Multiset ℝ) (hI : IsInstance I)
    (P : Multiset (Multiset ℝ)) (hP : Alg1Run ε I P) :
    IsPacking I P ∧
      (Multiset.card P : ℝ) ≤ (1 + 2 * ε) * (OPT I : ℝ) + 1 / (2 * ε ^ 2) + 3 := by sorry
end KKBinPacking.LinearGrouping
