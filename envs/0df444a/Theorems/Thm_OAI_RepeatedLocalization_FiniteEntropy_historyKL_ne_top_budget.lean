-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_historyKL_ne_top_budget
-- name    : OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:58:21.640193+00:00
-- url     : https://prove2.me/theorems/6941c3f5-55f2-4c5e-961f-33faaacec290
-- title:
--   Entropy budget for the conditional law on a single localization history
-- statement:
--   A *dyadic cell* $Q$ of $\mathbb R^n$ consists of a level $\ell(Q)\in\mathbb N$ and an index vector $k\in\{0,1,\dots,2^{\ell(Q)}-1\}^n$; its point set is the half-open box $C_Q=\prod_{a=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_a}{2^{\ell(Q)}\sqrt n},\,-\tfrac{1}{2\sqrt n}+\tfrac{k_a+1}{2^{\ell(Q)}\sqrt n}\big)$, a dyadic subcube of the cube $[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n})^n$. A cell $R$ is a *descendant* of $Q$ if $\ell(R)\ge\ell(Q)$ and $C_R\subseteq C_Q$.
--
--   For a cell $Q$, $\mathcal U_Q$ denotes the uniform law on $C_Q$ (Lebesgue measure conditioned on $C_Q$), and $\mathrm{KL}(\mu\,\|\,\nu)\in[0,\infty]$ denotes the Kullback–Leibler divergence.
--
--   For a measure $\mu$ on $\mathbb R^n$ and a cell $S$, a descendant $R$ of $S$ with $\ell(R)>\ell(S)$ is *heavy* (for $\mu$ below $S$) if $\mu(C_R)>2^{-n(\ell(R)-\ell(S))/2}$, and *first heavy* if it is heavy and no heavy cell other than $R$ itself has $R$ as a descendant. The *residual region* $\mathrm{Res}_\mu(S)$ is $C_S$ minus the union of the first heavy cells.
--
--   Given a measure $P$ on $\mathbb R^n$ and a cell $Q$, the localization procedure works with *states*: a state $s$ consists of a cell $S_s$, an event $E_s\subseteq\mathbb R^n$ and a flag saying whether $s$ is *active* or *stopped*. Write $\mu_s=P(\cdot\mid E_s)$ for the conditional law and $q(s)=\mu_s\big(\mathrm{Res}_{\mu_s}(S_s)\big)$ for the conditional mass of the residual region. A *letter* is either a cell $R$ or the symbol $\bot$, and a *log* is a finite word of letters. Reading a letter leaves a stopped state unchanged and acts on an active state $s$ as follows: the letter $R$ produces the active state with cell $R$ and event $E_s\cap C_R$ if $R$ is first heavy for $\mu_s$ below $S_s$ (and event $\varnothing$ otherwise); the letter $\bot$ keeps the cell, replaces the event by $E_s\cap\mathrm{Res}_{\mu_s}(S_s)$, and stops exactly when $q(s)\ge\tfrac12$. For a log $h=a_1\cdots a_m$ let $s_0=(Q,C_Q,\text{active})$ and let $s_i$ be obtained from $s_{i-1}$ by reading $a_i$; the state of $h$ is $s_h=s_m$, and we abbreviate $E_h=E_{s_h}$ and $S_h=S_{s_h}$.
--
--   For a reward function $r(s,a)$ on states and letters, the reward accumulated along a log $h=a_1\cdots a_m$ is $\mathcal R_r(h)=\sum_{i=1}^{m}r(s_{i-1},a_i)$. The *complement reward* is $c(s,a)=-\log q(s)$ if $s$ is active and $a=\bot$, and $c(s,a)=0$ otherwise.
--
--   Let $n\ge1$, let $P$ be a probability measure on $\mathbb R^n$ and let $Q$ be a cell with $P\ll\mathcal U_Q$ and $\mathrm{KL}(P\,\|\,\mathcal U_Q)<\infty$. Let $h$ be a log with $P(E_h)\neq0$. Then:
--
--   1. the conditional law on $E_h$ has finite divergence from the uniform law on the current cell, $\mathrm{KL}\big(P(\cdot\mid E_h)\,\|\,\mathcal U_{S_h}\big)<\infty$;
--   2. this divergence, plus $\frac{n\log2}{2}$ per level of descent, satisfies the budget
--
--   $$
--   P(E_h)\Big[\mathrm{KL}\big(P(\cdot\mid E_h)\,\big\|\,\mathcal U_{S_h}\big)+\frac{n\log2}{2}\big(\ell(S_h)-\ell(Q)\big)\Big]\;\le\;\int_{E_h}\log\frac{dP}{d\mathcal U_Q}\,dP\;+\;P(E_h)\,\mathcal R_c(h).
--   $$
--
--   This is the entropy budget of one history: the divergence of the conditional law on $E_h$ from the uniform law on the current cell, together with a reward of $\frac{n\log2}{2}$ per level of depth, is paid for by the part of the log-likelihood ratio carried by $E_h$ and by the complement rewards collected along $h$. Summed over the histories of a truncated run it gives the expected cost bound of the procedure, and its first part shows that the terminal conditional laws have finite divergence.
--
--   **Formalization Note** The divergence of the conditional law is `historyKL P Q h`, and the bracket on the left is `historyCost P Q h`, in which the divergence is converted to a real number with `toReal` (legitimate by the first claim) and `entropySlope n` $=\frac{n\log2}{2}$; the level difference is a natural-number subtraction. The integrand on the right is `llr P (uniformCell Q)`, the logarithm of the real-valued Radon–Nikodym derivative, and $\mathcal R_c(h)$ is `rewardLog P Q (complementReward P) h`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/EntropyBudget.lean#L30-L49

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Definitions.Def_OAI_Probability_Localization_EntropyBudget

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.historyKL_ne_top_budget {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    historyKL P Q h ≠ ∞ ∧
    (P (state P Q h).event).toReal * historyCost P Q h ≤
      (∫ z in (state P Q h).event,llr P (uniformCell Q) z ∂P) +
        (P (state P Q h).event).toReal * rewardLog P Q (complementReward P) h := by sorry
