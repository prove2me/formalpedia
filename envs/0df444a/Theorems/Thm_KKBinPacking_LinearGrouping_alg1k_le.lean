-- Prove2me | Theorems.Thm_KKBinPacking_LinearGrouping_alg1k_le
-- name    : KKBinPacking.LinearGrouping.alg1k_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T11:22:48.61711+00:00
-- url     : https://prove2.me/theorems/39a9c98f-b27b-4786-924f-688d522801a4
-- title:
--   Proof of Theorem 3, steps (ii)–(iii), corrected — $k \le 2\varepsilon\,OPT(I) + 1$
-- statement:
--   Let $\varepsilon > 0$ and let $I$ be an instance. Throughout, $J$ is the instance of Step 1 of ALGORITHM 1 (the pieces larger than $\max(1/n(I), \varepsilon/2)$), $k = \lceil n(J)\varepsilon^2\rceil$, and $K$, $K'$ are the outputs of linear grouping of $J$ with parameter $k$. Then
--
--   $$
--   k = \lceil n(J)\varepsilon^2\rceil \le 2\varepsilon\,OPT(I) + 1 .
--   $$
--
--   This bounds the number of bins used in Step 3 of ALGORITHM 1 for the pieces of $K'$.
--
--   **Formalization Note** The paper prints (ii) $OPT(J) \ge SIZE(J) \ge \varepsilon\, n(J)$ and (iii) $k \le \varepsilon\,OPT(J) + 1 \le \varepsilon\,OPT(I) + 1$. Step (ii) is false: the pieces of $J$ exceed $\varepsilon/2$, not $\varepsilon$, so only $SIZE(J) \ge (\varepsilon/2)\,n(J)$ holds. For $\varepsilon = 1/10$ and $I$ consisting of $19\,000$ pieces of size $0.051$ one has $J = I$, $k = 190$, $OPT(I) = 1000$, and $SIZE(J) = 969 < \varepsilon\, n(J) = 1900$, while $\varepsilon\,OPT(I) + 1 = 101 < 190$. The statement here is the bound the proof yields once (ii) is corrected.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 316, Theorem 3, proof steps (ii)–(iii) (left column), corrected

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_LinearGrouping_LinGroup
import Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
open KKBinPacking.Shared

namespace KKBinPacking.LinearGrouping
theorem alg1k_le (ε : ℝ) (hε : 0 < ε) (I : Multiset ℝ) (hI : IsInstance I) :
    (alg1k ε I : ℝ) ≤ 2 * ε * (OPT I : ℝ) + 1 := by sorry
end KKBinPacking.LinearGrouping
