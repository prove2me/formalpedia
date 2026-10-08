-- Prove2me | Theorems.Thm_MNLBandit_LowerBound_lemma_E_1
-- name    : MNLBandit.LowerBound.lemma_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:10.99599+00:00
-- url     : https://prove2.me/theorems/14fc1112-2106-4e76-bfff-a3959db03c41
-- title:
--   Lemma E.1, p. 57 — KL divergence of Ber(α) from Ber(α + ϵ) is at most 4ϵ²/α
-- statement:
--   For $p\in[0,1]$ and $q\in(0,1)$ write $\mathrm{kl}(p,q)=p\log\frac pq+(1-p)\log\frac{1-p}{1-q}$ for the Kullback–Leibler divergence between Bernoulli distributions with parameters $p$ and $q$ (natural logarithm).
--
--   Let $\alpha>0$ and $\epsilon>0$ with $\alpha+\epsilon\le 3/4$. Then
--
--   $$
--   \mathrm{kl}(\alpha,\alpha+\epsilon)\le\frac4\alpha\,\epsilon^2 .
--   $$
--
--   This is the direction used in the guessing lemma E.2, through the chain rule over the pulls of the biased coin.
--
--   **Formalization Note** The lemma names $p=\mathrm{Ber}(\alpha+\epsilon)$ and $q=\mathrm{Ber}(\alpha)$, but its proof computes $KL(\mathrm{Ber}(\alpha)\|\mathrm{Ber}(\alpha+\epsilon))$, the direction used in Lemma E.2; this corrected reading is stated. The page's text says "bounded by $4K\epsilon^2$" and the display $\frac4\alpha\epsilon^2$; the display's constant is used. The page has no hypothesis on $\alpha,\epsilon$; its last step needs a small $\alpha$, and the bound fails when $\alpha+\epsilon$ is close to $1$. The added hypotheses $0<\alpha$, $0<\epsilon$, $\alpha+\epsilon\le3/4$ make the inequality true and cover every use in the paper, where $\alpha$ is a small constant.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 57, Lemma E.1

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

namespace MNLBandit.LowerBound

theorem lemma_E_1 (α ϵ : ℝ) (hα : 0 < α) (hϵ : 0 < ϵ) (hαϵ : α + ϵ ≤ 3 / 4) :
    RegretBandits.Stochastic.klBern α (α + ϵ) ≤ 4 / α * ϵ ^ 2 := by sorry

end MNLBandit.LowerBound
