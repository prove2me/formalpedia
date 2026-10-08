-- Prove2me | Theorems.Thm_OnlineLearningOCO_Agnostic_corollary_3_8
-- name    : OnlineLearningOCO.Agnostic.corollary_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:07.127185+00:00
-- url     : https://prove2.me/theorems/2217c8ad-fe6f-45ae-90b9-7fdc5c8bf081
-- title:
--   Corollary 3.8 — some Expert(i₁,…,i_L) with L ≤ Ldim(H) makes no more mistakes than the best h ∈ H
-- statement:
--   Let $(x_1,y_1),\dots,(x_T,y_T)$ be a sequence of labelled examples with $y_t \in \{0,1\}$, and let $H$ be a hypothesis class with $\operatorname{Ldim}(H) < \infty$. Then there exist $L \le \operatorname{Ldim}(H)$ and indices $1 \le i_1 < \dots < i_L \le T$ such that the number of mistakes of Expert$(i_1,\dots,i_L)$ on the sequence satisfies
--
--   $$
--   \#\{t \le T : \hat y_t \ne y_t\} \le \min_{h\in H} \sum_{t=1}^T |h(x_t) - y_t|.
--   $$
--
--   This is the form of Lemma 3.7 used by the regret analysis: the best expert of the finite family is at least as good as the best hypothesis of the class.
--
--   **Formalization Note** The minimum over $h \in H$ is stated as "for every $h \in H$", which is equivalent; for $H = \emptyset$ the claim is vacuous. Rounds are 0-based, $I \subseteq \{0,\dots,T-1\}$ with $|I| \le \operatorname{Ldim}(H)$. The loss $\sum_t |h(x_t) - y_t|$ is the published `cumLossHyp`.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 167, Corollary 3.8

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_OnlineLearningOCO_Agnostic_expertAlg

namespace OnlineLearningOCO.Agnostic

open UnderstandingML

/-- Corollary 3.8, p. 167. Let `S = ((x₁,y₁),…,(x_T,y_T))` be a sequence of examples and `H` a
hypothesis class with `Ldim(H) < ∞`. There is a set `I ⊆ {0,…,T−1}` of (0-based) rounds with
`|I| ≤ Ldim(H)` such that Expert(I) makes at most `∑_t |h(x_t) − y_t|` mistakes on `S` for every
`h ∈ H`, hence at most `min_{h ∈ H} ∑_t |h(x_t) − y_t|` mistakes. -/
theorem corollary_3_8 {X : Type*} (H : Set (X → Bool)) (hH : ldim H < ⊤) {T : ℕ}
    (S : Fin T → X × Bool) :
    ∃ I : Finset ℕ, I ⊆ Finset.range T ∧ (I.card : ℕ∞) ≤ ldim H ∧
      ∀ h ∈ H, (mistakes (expertAlg H I) S : ℝ) ≤ cumLossHyp h S := by sorry

end OnlineLearningOCO.Agnostic
