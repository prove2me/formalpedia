-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_theorem_1
-- name    : MultiPurchase.Hardness.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:10.019234+00:00
-- url     : https://prove2.me/theorems/3646de92-4394-4857-99a2-3c937926b611
-- title:
--   Theorem 1, p. 17 — under BundleMVL-2, deciding max_C R₂(C) ≥ κ is NP-complete (relative to SIMPLE MAX CUT)
-- statement:
--   **Theorem 1 (Hardness result for BundleMVL-2).** Under the BundleMVL-2 model, the decision version of the unconstrained revenue optimization problem (5) is NP-complete.
--
--   Precisely: assume that SIMPLE MAX CUT is NP-complete. Then the language of instances $(r,V,v_0,\kappa)$ — rational revenues $r_i>0$, weights $V_{\{i\}},V_{\{i,j\}}\ge 0$, no-purchase weight $v_0>0$ and threshold $\kappa$ — for which some recommendation set $C\subseteq W$ satisfies
--   $$R_2(C)=\frac{\sum_{i\in C} r_iV_{\{i\}}+\sum_{i\in C}\sum_{j\in C,\,j>i}(r_i+r_j)V_{\{i,j\}}}{v_0+\sum_{i\in C}V_{\{i\}}+\sum_{i\in C}\sum_{j\in C,\,j>i}V_{\{i,j\}}}\ \ge\ \kappa$$
--   is NP-complete.
--
--   The result shows that, unlike the single-purchase multinomial logit model, revenue maximization under a multi-purchase logit model with bundles of size two admits no polynomial-time exact algorithm unless P = NP; it motivates the paper's binary-search and heuristic algorithms.
--
--   **Formalization Note** NP-completeness is Cook's Definition 4 (membership in NP and polynomial-time reducibility of every NP language). The NP-completeness of SIMPLE MAX CUT (Karp 1972; Garey and Johnson, problem ND16) is a hypothesis: the paper invokes it ("a reduction from Max-Cut") and the platform has no proof of it. Parameters are rational so that instances have finite binary codes, and weights may be zero as in the paper's own construction.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17 (PDF 17), Theorem 1; proof, Appendix pp. 4–5 (PDF 36–37)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

/-- Theorem 1, p. 17, relative to the NP-completeness of SIMPLE MAX CUT: under the BundleMVL-2
model, the decision version of the unconstrained revenue optimization problem (5) is
NP-complete. -/
theorem theorem_1 (hMC : NPComplete maxCutLang) : NPComplete bundleLang := by sorry

end MultiPurchase.Hardness
