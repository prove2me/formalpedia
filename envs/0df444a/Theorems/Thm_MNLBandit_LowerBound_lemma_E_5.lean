-- Prove2me | Theorems.Thm_MNLBandit_LowerBound_lemma_E_5
-- name    : MNLBandit.LowerBound.lemma_E_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:29.66027+00:00
-- url     : https://prove2.me/theorems/81c05184-ddee-4866-8ef9-e05bccb17753
-- title:
--   Lemma E.5, p. 61 — KL between the choice laws over T periods under v₁ = 1/2 and v₁ = 1/2 + ϵ is at most 4Tϵ²
-- statement:
--   Let $N\ge2$, $T\ge1$, and $\epsilon=\sqrt{1/(32T)}$ as in Definition E.1. Let $\mathcal A_{\mathrm{MNL}}$ be a policy that offers at each period $t$ an assortment $S_t\subseteq\{1,\dots,N\}$ determined by the past choices $c_1,\dots,c_{t-1}$ of the customers. On the instance $\hat I_{\mathrm{MNL}}$ ($v_0=1$, $v_i=\frac12$ for $i\ge2$), let $\mathbb P_0$ and $\mathbb P_1$ be the laws of the choice sequence $\mathbf c=(c_1,\dots,c_T)\in\{0,1,\dots,N\}^T$ when $v_1=\frac12$ and $v_1=\frac12+\epsilon$ respectively, i.e. $\mathbb P_b(\mathbf c)=\prod_{t=1}^{T}p^{(b)}_{c_t}(S_t)$ with the MNL probabilities (2.1). Then
--
--   $$
--   \mathrm{KL}(\mathbb P_0\|\mathbb P_1)=\sum_{\mathbf c\in\{0,1,\dots,N\}^T}\mathbb P_0(\mathbf c)\log\frac{\mathbb P_0(\mathbf c)}{\mathbb P_1(\mathbf c)}\le4T\epsilon^2 .
--   $$
--
--   Through Pinsker's inequality this bounds how differently the policy can behave under the two values of $v_1$, which drives the $K=N$ case of Theorem 2.
--
--   **Formalization Note** The policy is deterministic, as in the lemma's proof ("$S_t$ is completely determined by the reward history $c_1,\dots,c_{t-1}$", p. 61). The page's (E.9) writes $\mathcal P(\mathbf c)$ for $\mathbb P_0(\mathbf c)$. The Kullback–Leibler divergence is the published discrete divergence, valued in $[0,\infty]$ ($+\infty$ without absolute continuity). The horizon $T\ge1$ defines $\epsilon$ exactly as in Definition E.1; $N\ge2$ ensures the instance's second product exists. Periods and products are 0-based; no-purchase is `none`.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 61, Lemma E.5, (E.9)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_MNLBandit_LowerBound_Setting

namespace MNLBandit.LowerBound

theorem lemma_E_5 (N T : ℕ) (hN : 2 ≤ N) (hT : 1 ≤ T) (π : MNLBandit.UCB.Policy N) :
    FoundationsRL.GeneralDM.klDivDiscrete
        (histProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v π T)
        (histProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v π T) ≤
      ENNReal.ofReal (4 * T * (Real.sqrt (1 / (32 * (T : ℝ)))) ^ 2) := by sorry

end MNLBandit.LowerBound
