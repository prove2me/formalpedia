-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_path_label_surprisal
-- name    : OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:51:50.429031+00:00
-- url     : https://prove2.me/theorems/debaaf10-d288-49ba-85ff-be94abdadc48
-- title:
--   Surprisal of a localization history is at most its depth cost plus its complement rewards
-- statement:
--   A *dyadic cell* $Q$ of $\mathbb R^n$ consists of a level $\ell(Q)\in\mathbb N$ and an index vector $k\in\{0,1,\dots,2^{\ell(Q)}-1\}^n$; its point set is the half-open box $C_Q=\prod_{a=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_a}{2^{\ell(Q)}\sqrt n},\,-\tfrac{1}{2\sqrt n}+\tfrac{k_a+1}{2^{\ell(Q)}\sqrt n}\big)$, a dyadic subcube of the cube $[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n})^n$. A cell $R$ is a *descendant* of $Q$ if $\ell(R)\ge\ell(Q)$ and $C_R\subseteq C_Q$.
--
--   For a measure $\mu$ on $\mathbb R^n$ and a cell $S$, a descendant $R$ of $S$ with $\ell(R)>\ell(S)$ is *heavy* (for $\mu$ below $S$) if $\mu(C_R)>2^{-n(\ell(R)-\ell(S))/2}$, and *first heavy* if it is heavy and no heavy cell other than $R$ itself has $R$ as a descendant. The *residual region* $\mathrm{Res}_\mu(S)$ is $C_S$ minus the union of the first heavy cells.
--
--   Given a measure $P$ on $\mathbb R^n$ and a cell $Q$, the localization procedure works with *states*: a state $s$ consists of a cell $S_s$, an event $E_s\subseteq\mathbb R^n$ and a flag saying whether $s$ is *active* or *stopped*. Write $\mu_s=P(\cdot\mid E_s)$ for the conditional law and $q(s)=\mu_s\big(\mathrm{Res}_{\mu_s}(S_s)\big)$ for the conditional mass of the residual region. A *letter* is either a cell $R$ or the symbol $\bot$, and a *log* is a finite word of letters. Reading a letter leaves a stopped state unchanged and acts on an active state $s$ as follows: the letter $R$ produces the active state with cell $R$ and event $E_s\cap C_R$ if $R$ is first heavy for $\mu_s$ below $S_s$ (and event $\varnothing$ otherwise); the letter $\bot$ keeps the cell, replaces the event by $E_s\cap\mathrm{Res}_{\mu_s}(S_s)$, and stops exactly when $q(s)\ge\tfrac12$. For a log $h=a_1\cdots a_m$ let $s_0=(Q,C_Q,\text{active})$ and let $s_i$ be obtained from $s_{i-1}$ by reading $a_i$; the state of $h$ is $s_h=s_m$, and we abbreviate $E_h=E_{s_h}$ and $S_h=S_{s_h}$.
--
--   Let $n\in\mathbb N$, let $P$ be a probability measure on $\mathbb R^n$ and let $Q$ be a cell with $P(C_Q)=1$. Let $h=a_1\cdots a_m$ be a log with states $s_0,\dots,s_m=s_h$ as above, and let the *complement reward* be $c(s,a)=-\log q(s)$ if $s$ is active and $a=\bot$, and $c(s,a)=0$ otherwise. If $P(E_h)\neq0$, then
--
--   $$
--   -\log P(E_h)\;\le\;\frac{n\log 2}{2}\,\big(\ell(S_h)-\ell(Q)\big)+\sum_{i=1}^{m}c(s_{i-1},a_i).
--   $$
--
--   The left-hand side is the surprisal of the event $E_h$ selected by the history $h$. The inequality charges it at the rate $\frac{n\log2}{2}$ per dyadic level that the history descends below $Q$, plus the complement rewards collected at the $\bot$ letters. It is the pathwise ingredient of the entropy budget of the localization procedure: combined with the chain rule for the relative entropy of conditioned measures, it bounds the divergence of the conditional law on $E_h$ from the uniform law on the current cell.
--
--   **Formalization Note** The level difference is the natural-number subtraction `(state P Q h).cell.1 - Q.1` cast to a real number; it is truncated at $0$, but for a history of positive probability the current cell is a descendant of $Q$, so no truncation occurs. Probabilities are extended nonnegative reals converted with `toReal`, $q(s)$ is `complementMass P s`, and the reward sum is `rewardLog P Q (complementReward P) h`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Rewards.lean#L123-L171

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.path_label_surprisal {n : ℕ} (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hroot : P (cellSet Q) = 1) (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    -Real.log (P (state P Q h).event).toReal ≤
      ((n:ℝ)*Real.log 2/2)*((state P Q h).cell.1-Q.1 : ℕ) + rewardLog P Q (complementReward P) h := by sorry
