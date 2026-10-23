-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_4
-- name    : MNLTrisection.Adaptive.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:40.260292+00:00
-- url     : https://prove2.me/theorems/54f8c75d-e128-4076-b769-40ba84f5c7f3
-- title:
--   Lemma 4, p. 8 — to the left of θ*, F(θ) ≥ θ and F(θ) ≤ F(θ⁺)
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Let $F(\theta) = R(\{i : r_i \ge \theta\})$, $F(\theta^+)$ its right limit, and $\theta^* = F^* = \sup_{\theta\ge 0} F(\theta)$. For every $\theta \le \theta^*$,
--   $$F(\theta) \ge \theta \quad\text{and}\quad F(\theta) \le F(\theta^+).$$
--
--   To the left of the fixed point the potential lies above the diagonal, so the comparison of $F(y)$ with $y$ is a one-sided test for the position of $\theta^*$.
--
--   **Formalization Note** $\theta^*$ is $F^*$. The page considers $\theta \in [0,1]$; the statement is for every real $\theta \le \theta^*$ (for $\theta < 0$ both claims hold since $\mathcal L_\theta = [N]$ near $\theta$), which includes the page's range.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 8, Lemma 4; proof in Supplement p. 2 (PDF 21)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Lemma 4** (p. 8). For any `θ ≤ θ*`, `F(θ) ≥ θ` and `F(θ) ≤ F(θ⁺)`. -/
theorem lemma_4 {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (θ : ℝ) (hθ : θ ≤ thetaStar v r) :
    θ ≤ F v r θ ∧ F v r θ ≤ Function.rightLim (F v r) θ := by sorry

end MNLTrisection.Adaptive
