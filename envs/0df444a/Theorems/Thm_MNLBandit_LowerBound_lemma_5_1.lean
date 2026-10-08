-- Prove2me | Theorems.Thm_MNLBandit_LowerBound_lemma_5_1
-- name    : MNLBandit.LowerBound.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:57:56.413403+00:00
-- url     : https://prove2.me/theorems/7e5df205-470d-4380-b298-56f102303099
-- title:
--   Lemma 5.1, p. 15 — every online algorithm has expected regret at least ϵT/6 on I_MAB
-- statement:
--   Let $N\ge2$ arms, a horizon $T\ge1$, $\alpha>0$, and
--
--   $$
--   \epsilon=\frac1{100}\sqrt{\frac{N\alpha}{T}},
--   $$
--
--   with $2\alpha+\epsilon\le1$. On the randomized Bernoulli instance $I_{\mathrm{MAB}}$ (Definition 5.1: a hidden arm $j$, uniform on $\{1,\dots,N\}$, has mean $\alpha+\epsilon$ and every other arm mean $\alpha$), every online algorithm $\mathcal A$, deterministic or randomized, that plays arm $\mathcal A_t$ at time $t$ satisfies
--
--   $$
--   \mathrm{Reg}_{\mathcal A}(T,\mu)=\mathbb E\Big[\sum_{t=1}^{T}(\mu_j-\mu_{\mathcal A_t})\Big]\ge\frac{\epsilon T}{6},
--   $$
--
--   where the expectation is over the hidden arm $j$ and over the rewards of the pulled arms (and the algorithm's own randomization).
--
--   This MAB lower bound is what the reduction of §5.2 transfers to the MNL-Bandit problem under a cardinality constraint.
--
--   **Formalization Note** The page assumes only $\alpha<1$. That is not enough: for $\alpha$ close to $1$ the biased arm is identified after few pulls and the bound fails; the proof sets "$\alpha$ to be a small enough constant" (p. 19). The added hypothesis $2\alpha+\epsilon\le1$ (which implies $\alpha<1$) and $\alpha>0$ restore it. $T\ge1$ is added because $\epsilon$ has $T$ in a denominator. The printed proof's line "Let $\epsilon=\sqrt{N/(60\alpha T)}$" contradicts Definition 5.1; the lemma is stated with Definition 5.1's $\epsilon$, which satisfies the proof's requirement $T\le N\alpha/(60\epsilon^2)$. The printed $N\ge2$ is kept although the printed proof (via Lemma E.2) needs $N\ge12$.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 15, Lemma 5.1 and Definition 5.1; proof p. 58

import Mathlib
import Definitions.Def_MNLBandit_LowerBound_BernoulliMAB

namespace MNLBandit.LowerBound

theorem lemma_5_1 (N : ℕ) (hN : 2 ≤ N) (α : ℝ) (hα : 0 < α) (T : ℕ) (hT : 1 ≤ T)
    (hαϵ : 2 * α + epsMAB N α T ≤ 1) (A : MABAlg N) (hA : IsMABAlg A) :
    epsMAB N α T * T / 6 ≤ regretIMAB A α (epsMAB N α T) T := by sorry

end MNLBandit.LowerBound
