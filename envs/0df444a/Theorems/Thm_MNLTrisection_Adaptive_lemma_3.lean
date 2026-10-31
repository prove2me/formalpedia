-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_3
-- name    : MNLTrisection.Adaptive.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:23.416312+00:00
-- url     : https://prove2.me/theorems/62619358-ebb3-4493-9cfd-9a456fb6db0d
-- title:
--   Lemma 3, p. 8 — to the right of θ*, F(θ) ≤ θ and F(θ) ≥ F(θ⁺)
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Let $F(\theta) = R(\{i : r_i \ge \theta\})$, $F(\theta^+)$ its right limit, and $\theta^* = F^* = \sup_{\theta\ge 0} F(\theta)$. For every $\theta \ge \theta^*$,
--   $$F(\theta) \le \theta \quad\text{and}\quad F(\theta) \ge F(\theta^+).$$
--
--   To the right of the fixed point the potential lies below the diagonal, so observing $F(y) < y$ tells the policy that $y$ is too high.
--
--   **Formalization Note** $\theta^*$ is $F^*$, the value Lemma 2 assigns to the fixed point; no positivity of $F^*$ is needed here.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 8, Lemma 3; proof in Supplement p. 2 (PDF 21)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Lemma 3** (p. 8). For any `θ ≥ θ*`, `F(θ) ≤ θ` and `F(θ) ≥ F(θ⁺)`. -/
theorem lemma_3 {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (θ : ℝ) (hθ : thetaStar v r ≤ θ) :
    F v r θ ≤ θ ∧ Function.rightLim (F v r) θ ≤ F v r θ := by sorry

end MNLTrisection.Adaptive
