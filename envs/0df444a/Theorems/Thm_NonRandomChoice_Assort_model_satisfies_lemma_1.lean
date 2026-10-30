-- Prove2me | Theorems.Thm_NonRandomChoice_Assort_model_satisfies_lemma_1
-- name    : NonRandomChoice.Assort.model_satisfies_lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:30.929399+00:00
-- url     : https://prove2.me/theorems/56728d2b-c5b1-4ed1-a813-8c1892084ff5
-- title:
--   Proof of Theorem 5, pp. 14, 29 — the model with a deterministic product utility satisfies the hypotheses of Lemma 1
-- statement:
--   Consider the choice model with one deterministic product utility: products $\mathcal N=\{1,\dots,N\}$, a product $i'\in\mathcal N$ with deterministic utility, scale $\mu>0$, utilities $u_i$, $u_0$, and the choice probabilities $q_i(S)$ given by the MNL formula when $i'\notin S$ and by model (1) when $i'\in S$ (see the definition item). Then:
--   1. the model is **regular**: choice probabilities are nonnegative, vanish off the offer set, sum to at most one, and the choice probability of every offered product and of the no-purchase option does not increase when the offer set is enlarged;
--   2. every choice probability is a convex function of the no-purchase probability: for each product $i$ there are a convex set $D_i$ and a function $f_i$, nonnegative and convex on $D_i$, with $q_0(S)\in D_i$ and
--   $$q_i(S)=f_i\bigl(q_0(S)\bigr)\qquad\text{for every offer set }S\ni i;$$
--   3. the revenue (12) is the revenue of these choice probabilities: $R(S)=\sum_{i\in S}p_i\,q_i(S)$ for all prices $p$ and all $S\subseteq\mathcal N$.
--
--   This is the step the paper announces on p. 14 and concludes on p. 29: combined with Lemma 1 it gives Theorem 5.
--
--   **Formalization Note** Regularity is the published `RevenueOrdered.Ratio.IsRegular`, which includes monotonicity of the no-purchase probability; the printed proof does not verify regularity explicitly. The hypothesis of Lemma 1 is reproduced exactly (functions `f`, sets `D`), so that the two milestones compose. For $i\neq i'$ one may take $f_i(x)=(a_i/a_0)x$; for $i'$ the inverse of $h_{a_0\Lambda}$ of the previous milestones.
-- source:
--   Wang, What Is the Impact of Non-Randomness on Random Choice Models?, SSRN 3579781 (PDF sha256 93af6c3d…), p. 14 (announcement after Theorem 5) and p. 29 (proof of Theorem 5, last paragraph)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_NonRandomChoice_Assort_Model

namespace NonRandomChoice.Assort

theorem model_satisfies_lemma_1 {N : ℕ} (μ u0 : ℝ) (hμ : 0 < μ) (u : Fin N → ℝ)
    (ip : Fin N) :
    RevenueOrdered.Ratio.IsRegular (choiceProb μ u0 u ip) ∧
      (∃ (f : Fin N → ℝ → ℝ) (D : Fin N → Set ℝ),
        (∀ i, ConvexOn ℝ (D i) (f i)) ∧
        (∀ i, ∀ x ∈ D i, 0 ≤ f i x) ∧
        (∀ (S : Finset (Fin N)) (i : Fin N), i ∈ S →
          RevenueOrdered.Ratio.noPurchase (choiceProb μ u0 u ip) S ∈ D i ∧
            choiceProb μ u0 u ip i S =
              f i (RevenueOrdered.Ratio.noPurchase (choiceProb μ u0 u ip) S))) ∧
      (∀ (p : Fin N → ℝ) (S : Finset (Fin N)),
        revenue12 μ u0 u ip p S = RevenueOrdered.Ratio.revenue (choiceProb μ u0 u ip) p S) := by sorry

end NonRandomChoice.Assort
