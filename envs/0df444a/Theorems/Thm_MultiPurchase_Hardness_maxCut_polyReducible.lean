-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_maxCut_polyReducible
-- name    : MultiPurchase.Hardness.maxCut_polyReducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:58.359567+00:00
-- url     : https://prove2.me/theorems/312a31f1-731b-47f1-bfb4-8223a3bc368d
-- title:
--   Theorem 1, p. 17, hardness half — SIMPLE MAX CUT ≤ₚ the BundleMVL-2 decision problem
-- statement:
--   SIMPLE MAX CUT (given a simple graph $G$ and an integer $M$, does $G$ have a cut with at least $M$ edges?) is polynomial-time many-one reducible to the decision version of the unconstrained BundleMVL-2 revenue optimization problem (5):
--
--   $$\text{SIMPLE MAX CUT}\le_p\text{BundleMVL-2-DEC}.$$
--
--   This is the reduction of the proof of Theorem 1, as a polynomial-time map on instance codes.
--
--   **Formalization Note** Both problems are languages of binary codes over the alphabet $\{0,1,-,\#\}$: SIMPLE MAX CUT is the published `maxCutLang` (number of nodes, adjacency matrix, $M$); reducibility is Cook's Definition 3 (a function computable in polynomial time by a one-tape Turing machine that maps members to members and non-members to non-members, including strings that are not codes of any instance). The paper gives the construction but no running-time argument.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17 (PDF 17), Theorem 1; proof, Appendix pp. 4–5 (PDF 36–37)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

/-- Theorem 1, p. 17, hardness half (proof, Appendix pp. 4–5): SIMPLE MAX CUT reduces in
polynomial time to the decision version of the unconstrained BundleMVL-2 revenue problem (5). -/
theorem maxCut_polyReducible : PolyReducible maxCutLang bundleLang := by sorry

end MultiPurchase.Hardness
