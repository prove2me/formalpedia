-- Prove2me | Theorems.Thm_MNLBandit_LowerBound_lemma_E_4
-- name    : MNLBandit.LowerBound.lemma_E_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:20.852866+00:00
-- url     : https://prove2.me/theorems/d5e3f83f-e22e-4afc-b497-fa7cc77d3735
-- title:
--   Lemma E.4, p. 60 — one-step KL between MNL feedback with v₁ = 1/2 and v₁ = 1/2 + ϵ is at most 4ϵ²
-- statement:
--   Consider the MNL-Bandit instance $\hat I_{\mathrm{MNL}}$ of Definition E.1: $N$ products, no-purchase weight $v_0=1$, $v_i=\frac12$ for $i=2,\dots,N$, and $v_1$ equal to $\frac12$ or $\frac12+\epsilon$. For an offer set $S\subseteq\{1,\dots,N\}$ let $\mathcal P^S_0$ and $\mathcal P^S_1$ be the MNL choice distributions on $\{0,1,\dots,N\}$ when $v_1=\frac12$ and $v_1=\frac12+\epsilon$ respectively:
--
--   $$
--   \mathcal P^S_0(i)=\frac{1}{2+|S|}\times\begin{cases}0,& i\notin S\cup\{0\},\\ 2,& i=0,\\ 1,& i\in S,\end{cases}
--   \qquad
--   \mathcal P^S_1(i)=\frac{1}{2+|S|+2\epsilon\mathbb 1(1\in S)}\times\begin{cases}0,& i\notin S\cup\{0\},\\ 2,& i=0,\\ 1,& i\in S\setminus\{1\},\\ 1+2\epsilon,& i=1.\end{cases}
--   $$
--
--   Let $T\ge1$ and set $\epsilon=\sqrt{1/(32T)}$ as in Definition E.1. Then for every $S$,
--
--   $$
--   \mathrm{KL}\big(\mathcal P^S_0\,\big\|\,\mathcal P^S_1\big)=\sum_{i=0}^{N}\mathcal P^S_0(i)\log\frac{\mathcal P^S_0(i)}{\mathcal P^S_1(i)}\le4\epsilon^2 .
--   $$
--
--   It is the per-period step of the change-of-measure argument for the unconstrained case $K=N$ of Theorem 2.
--
--   **Formalization Note** $\mathcal P^S_b$ is the MNL choice probability (2.1) of the instance $\hat I_{\mathrm{MNL}}$ with the respective $v_1$; the two displays above are what (2.1) gives for $v_0=1$, $v_i=\frac12$. The Kullback–Leibler divergence is the published discrete divergence on a finite type, valued in $[0,\infty]$, which is $+\infty$ unless $\mathcal P^S_0$ is absolutely continuous with respect to $\mathcal P^S_1$ (here it always is). The horizon $T\ge1$ defines $\epsilon$ exactly as in Definition E.1; $N\ge2$ ensures the instance's second product exists. Products are 0-based: the paper's product 1 is index $0$.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 60, Lemma E.4, (E.8); p. 59, Definition E.1

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_MNLBandit_LowerBound_Setting

namespace MNLBandit.LowerBound

theorem lemma_E_4 (N T : ℕ) (hN : 2 ≤ N) (hT : 1 ≤ T) (S : Finset (Fin N)) :
    FoundationsRL.GeneralDM.klDivDiscrete
        (choiceProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) false).v S)
        (choiceProb (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v₀
          (instHat N (Real.sqrt (1 / (32 * (T : ℝ)))) true).v S) ≤
      ENNReal.ofReal (4 * (Real.sqrt (1 / (32 * (T : ℝ)))) ^ 2) := by sorry

end MNLBandit.LowerBound
