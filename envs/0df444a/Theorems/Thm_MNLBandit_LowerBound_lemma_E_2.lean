-- Prove2me | Theorems.Thm_MNLBandit_LowerBound_lemma_E_2
-- name    : MNLBandit.LowerBound.lemma_E_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:43.231692+00:00
-- url     : https://prove2.me/theorems/d2bab7b6-af0f-4339-90aa-8881e98c86c3
-- title:
--   Lemma E.2, p. 57 — for t ≤ Nα/(60ϵ²) at least N/3 hiding places j have 𝒫_j(a_t = j) ≤ 1/2
-- statement:
--   Consider $N$ coins (arms): when the biased coin is hidden at position $j$, coin $j$ shows $1$ with probability $\alpha+\epsilon$ and every other coin with probability $\alpha$. A guessing algorithm $\mathcal A$ is an online algorithm on these coins: at each time it chooses (possibly at random) a coin $a_t$ given the coins it chose before and their outputs, and sees the output of $a_t$. Write $\mathcal P_j$ for the law of its view when the biased coin is at position $j$.
--
--   Let $N\ge 12$, $\alpha>0$, $0<\epsilon\le\frac14$ with $2\alpha+\epsilon\le1$, and let $t\ge1$ be a time with
--
--   $$
--   t\le\frac{N\alpha}{60\,\epsilon^2}.
--   $$
--
--   Then there is a set $J\subseteq\{1,\dots,N\}$ with $|J|\ge N/3$ such that
--
--   $$
--   \forall j\in J,\qquad \mathcal P_j(a_t=j)\le\frac12 .
--   $$
--
--   In words: for a short horizon, at least a third of the possible hiding places of the biased coin are not guessed with probability more than $1/2$. This is the key step of the MAB lower bound (Lemma 5.1).
--
--   **Formalization Note** The time is written $t=s+1$, where $s$ is the number of rounds observed before $a_t$ is chosen; the hypothesis is $s+1\le N\alpha/(60\epsilon^2)$. The added hypotheses $0<\alpha$, $0<\epsilon$ and $2\alpha+\epsilon\le1$ are those of the instance $I_{\mathrm{MAB}}$ with a small $\alpha$. The printed proof's form of Pinsker's inequality, $\frac12\sqrt{2\log2\cdot KL}$, is smaller than the true $\sqrt{KL/2}$; with the true inequality and $\mathrm{kl}(\alpha,\alpha+\epsilon)\le\epsilon^2/\alpha$, which holds when $2\alpha+\epsilon\le1$, the printed $N\ge12$ suffices. The algorithm is randomized (behavioural), which includes the deterministic ones.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 57, Lemma E.2 (and the paragraph before it)

import Mathlib
import Definitions.Def_MNLBandit_LowerBound_BernoulliMAB

namespace MNLBandit.LowerBound

theorem lemma_E_2 (N : ℕ) (hN : 12 ≤ N) (α ϵ : ℝ) (hα : 0 < α) (hϵ : 0 < ϵ)
    (hϵ4 : ϵ ≤ 1 / 4) (hαϵ : 2 * α + ϵ ≤ 1)
    (A : MABAlg N) (hA : IsMABAlg A) (s : ℕ)
    (hs : (s : ℝ) + 1 ≤ (N : ℝ) * α / (60 * ϵ ^ 2)) :
    ∃ J : Finset (Fin N), (N : ℝ) / 3 ≤ J.card ∧
      ∀ j ∈ J, armProb A (imabMeans α ϵ j) s j ≤ 1 / 2 := by sorry

end MNLBandit.LowerBound
