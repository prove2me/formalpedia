-- Prove2me | Theorems.Thm_KKBinPacking_LinearGrouping_alg1_card_PJ_le
-- name    : KKBinPacking.LinearGrouping.alg1_card_PJ_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:24:25.666729+00:00
-- url     : https://prove2.me/theorems/5bc0f563-7301-4d91-abd6-6e6407096fe1
-- title:
--   Proof of Theorem 3, step (viii), corrected — Step 6 uses at most $(1+2\varepsilon)OPT(I) + 1/(2\varepsilon^2) + 5/2$ bins
-- statement:
--   Let $\varepsilon > 0$ and let $I$ be an instance. For every run of ALGORITHM 1, the packing of $J$ produced at Step 6 (the packing of $K$ from Step 5 together with the $|K'| \le k$ bins of Step 3, after reducing sizes) has at most
--
--   $$
--   (1+2\varepsilon)\,OPT(I) + \frac{1}{2\varepsilon^2} + \frac{5}{2}
--   $$
--
--   bins.
--
--   **Formalization Note** The paper prints the bound $\mathbf 1\cdot x + (m(K)+1)/2 + k \le (OPT(I)+1) + (1 + 1/\varepsilon^2)/2 + \varepsilon\,OPT(I) + 1$. Its last term uses the printed step (iii), which is false (see the milestone for steps (ii)–(iii)); with the corrected $k \le 2\varepsilon\,OPT(I) + 1$ the same chain gives the bound stated here.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 316, Theorem 3, proof step (viii) (left column), corrected

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_LinearGrouping_LinGroup
import Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
open KKBinPacking.Shared

namespace KKBinPacking.LinearGrouping
theorem alg1_card_PJ_le (ε : ℝ) (hε : 0 < ε) (I : Multiset ℝ) (hI : IsInstance I)
    (tr : Alg1Trace ε I) :
    (Multiset.card tr.PJ : ℝ) ≤ (1 + 2 * ε) * (OPT I : ℝ) + 1 / (2 * ε ^ 2) + 5 / 2 := by sorry
end KKBinPacking.LinearGrouping
