-- Prove2me | Theorems.Thm_KKBinPacking_LinearGrouping_alg1_numSizes_K_le
-- name    : KKBinPacking.LinearGrouping.alg1_numSizes_K_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T11:23:12.273999+00:00
-- url     : https://prove2.me/theorems/583b7d26-b164-4f3b-8b9c-523059416d9e
-- title:
--   Proof of Theorem 3, step (iv) — $m(K) \le 1/\varepsilon^2$
-- statement:
--   Let $\varepsilon > 0$ and let $I$ be an instance. Throughout, $J$ is the instance of Step 1 of ALGORITHM 1 (the pieces larger than $\max(1/n(I), \varepsilon/2)$), $k = \lceil n(J)\varepsilon^2\rceil$, and $K$, $K'$ are the outputs of linear grouping of $J$ with parameter $k$. Then the number of distinct sizes of $K$ satisfies
--
--   $$
--   m(K) \le \frac{1}{\varepsilon^2}.
--   $$
--
--   This controls the additive rounding loss $(m(K)+1)/2$ of Corollary 1 in Step 5.
--
--   **Formalization Note** The paper prints the chain $m(K) \le n(K)/k \le \dots \le 1/\varepsilon^2$. Its first link fails when the last group is short (for $n(J) = k + 1$ one has $n(K) = 1$ and $m(K) = 1 > 1/k$); the end of the chain, stated here, is true.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 316, Theorem 3, proof step (iv) (left column)

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_LinearGrouping_LinGroup
import Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
open KKBinPacking.Shared

namespace KKBinPacking.LinearGrouping
theorem alg1_numSizes_K_le (ε : ℝ) (hε : 0 < ε) (I : Multiset ℝ) (hI : IsInstance I) :
    (numSizes (alg1K ε I) : ℝ) ≤ 1 / ε ^ 2 := by sorry
end KKBinPacking.LinearGrouping
