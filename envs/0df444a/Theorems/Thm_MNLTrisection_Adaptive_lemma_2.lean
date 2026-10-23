-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_2
-- name    : MNLTrisection.Adaptive.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:14.37268+00:00
-- url     : https://prove2.me/theorems/56d8d07b-2010-41ea-900e-aa3c12a7c5f8
-- title:
--   Lemma 2, p. 8 — if F* > 0 the revenue potential has a positive fixed point θ* = F(θ*) = F*
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Let $F(\theta) = R(\{i : r_i \ge \theta\})$ and $F^* = \sup_{\theta \ge 0} F(\theta)$. If $F^* > 0$, there is $\theta^* > 0$ with
--   $$\theta^* = F(\theta^*) = F^*.$$
--
--   The fixed point locates the optimal revenue level: the trisection policy searches for it.
--
--   **Formalization Note** The hypothesis $F^* > 0$ (equivalently, $r_i v_i > 0$ for some $i$) is added: the proof (Supplement p. 1) uses "$F^* > 0$", and with all $v_i = 0$ the potential vanishes and no positive fixed point exists.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 8, Lemma 2; proof in Supplement p. 1 (PDF 20)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Lemma 2** (p. 8). If `F* > 0`, there is `θ* > 0` with `θ* = F(θ*) = F*`. -/
theorem lemma_2 {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < Fstar v r) :
    ∃ θ : ℝ, 0 < θ ∧ θ = F v r θ ∧ F v r θ = Fstar v r := by sorry

end MNLTrisection.Adaptive
