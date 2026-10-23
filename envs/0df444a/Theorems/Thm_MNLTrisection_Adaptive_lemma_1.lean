-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_1
-- name    : MNLTrisection.Adaptive.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:07.915622+00:00
-- url     : https://prove2.me/theorems/380e3369-2bf9-4062-b219-3a6069871088
-- title:
--   Lemma 1, p. 7 — some assortment maximizing the MNL revenue over all subsets is matched by a revenue level set
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$.
--
--   Some assortment $S^* \subseteq [N]$ is optimal among all subsets, and its revenue is attained by a level set $\mathcal L_\theta = \{i : r_i \ge \theta\}$ with $\theta \ge 0$:
--   $$R(S^*) = \max_{S \subseteq [N]} R(S) = \max_{\theta \ge 0} R(\mathcal L_\theta).$$
--
--   This classical fact of revenue management lets the policy search only among the at most $N$ revenue-ordered assortments.
--
--   **Formalization Note** The statement asserts that $S^*$ maximizes $R$ over all subsets and that $R(\mathcal L_\theta) = R(S^*)$ for some $\theta \ge 0$; since every level set is a subset, this is the equality of the two maxima. The paper's standing assumption $r_i > 0$ is relaxed to $r_i \ge 0$, as in Theorem 3.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 7, Lemma 1

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Lemma 1** (p. 7). Under the MNL model there is an assortment `S*` with
`R(S*) = max_{S ∈ 𝕊} R(S) = max_{S ∈ ℙ} R(S)`: `S*` maximizes `R` over all subsets, and some
level set `𝓛_θ` with `θ ≥ 0` attains the same revenue. -/
theorem lemma_1 {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Sstar : Finset (Fin N), (∀ S : Finset (Fin N), rev v r S ≤ rev v r Sstar) ∧
      ∃ θ : ℝ, 0 ≤ θ ∧ rev v r (levelSet r θ) = rev v r Sstar := by sorry

end MNLTrisection.Adaptive
