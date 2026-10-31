-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_corollary_1
-- name    : MNLTrisection.Adaptive.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:11.51254+00:00
-- url     : https://prove2.me/theorems/a74e4da5-65e7-4b18-854d-7c3fb7319ce4
-- title:
--   Corollary 1, p. 8 — the maximum F* of the revenue potential equals the optimal revenue R(S*)
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Let $F(\theta) = R(\{i : r_i \ge \theta\})$ be the revenue potential and $F^* = \sup_{\theta \ge 0} F(\theta)$. Then
--   $$F^* = R(S^*) = \max_{S \subseteq [N]} R(S).$$
--
--   The regret of any policy can therefore be measured against $F^*$, the maximum of a one-dimensional function.
--
--   **Formalization Note** $F^*$ is defined as the supremum (not as a maximum of the constants $c_i$ of Proposition 1, which is not formalized), and $R(S^*)$ as the maximum of $R$ over all subsets.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 8, definition of F* and Corollary 1

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Corollary 1** (p. 8). `F* = sup_{θ ≥ 0} F(θ)` equals the optimal revenue
`R(S*) = max_{S ⊆ [N]} R(S)`. -/
theorem corollary_1 {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) :
    Fstar v r = optRev v r := by sorry

end MNLTrisection.Adaptive
