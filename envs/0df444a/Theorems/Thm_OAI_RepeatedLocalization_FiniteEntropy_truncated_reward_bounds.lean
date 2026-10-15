-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_reward_bounds
-- name    : OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:57:17.578122+00:00
-- url     : https://prove2.me/theorems/7c2a5e03-7ac5-4240-9e12-05b6a0845aec
-- title:
--   Expected complement and continuation rewards are at most $1/e$ and $1/2$ times the expected number of attempts
-- statement:
--   A *dyadic cell* $Q$ of $\mathbb R^n$ consists of a level $\ell(Q)\in\mathbb N$ and an index vector $k\in\{0,1,\dots,2^{\ell(Q)}-1\}^n$; its point set is the half-open box $C_Q=\prod_{a=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_a}{2^{\ell(Q)}\sqrt n},\,-\tfrac{1}{2\sqrt n}+\tfrac{k_a+1}{2^{\ell(Q)}\sqrt n}\big)$, a dyadic subcube of the cube $[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n})^n$. A cell $R$ is a *descendant* of $Q$ if $\ell(R)\ge\ell(Q)$ and $C_R\subseteq C_Q$.
--
--   For a measure $\mu$ on $\mathbb R^n$ and a cell $S$, a descendant $R$ of $S$ with $\ell(R)>\ell(S)$ is *heavy* (for $\mu$ below $S$) if $\mu(C_R)>2^{-n(\ell(R)-\ell(S))/2}$, and *first heavy* if it is heavy and no heavy cell other than $R$ itself has $R$ as a descendant. The *residual region* $\mathrm{Res}_\mu(S)$ is $C_S$ minus the union of the first heavy cells.
--
--   Given a measure $P$ on $\mathbb R^n$ and a cell $Q$, the localization procedure works with *states*: a state $s$ consists of a cell $S_s$, an event $E_s\subseteq\mathbb R^n$ and a flag saying whether $s$ is *active* or *stopped*. Write $\mu_s=P(\cdot\mid E_s)$ for the conditional law and $q(s)=\mu_s\big(\mathrm{Res}_{\mu_s}(S_s)\big)$ for the conditional mass of the residual region. A *letter* is either a cell $R$ or the symbol $\bot$, and a *log* is a finite word of letters. Reading a letter leaves a stopped state unchanged and acts on an active state $s$ as follows: the letter $R$ produces the active state with cell $R$ and event $E_s\cap C_R$ if $R$ is first heavy for $\mu_s$ below $S_s$ (and event $\varnothing$ otherwise); the letter $\bot$ keeps the cell, replaces the event by $E_s\cap\mathrm{Res}_{\mu_s}(S_s)$, and stops exactly when $q(s)\ge\tfrac12$. For a log $h=a_1\cdots a_m$ let $s_0=(Q,C_Q,\text{active})$ and let $s_i$ be obtained from $s_{i-1}$ by reading $a_i$; the state of $h$ is $s_h=s_m$, and we abbreviate $E_h=E_{s_h}$ and $S_h=S_{s_h}$.
--
--   The *run* of a point $z\in\mathbb R^n$ is defined recursively: $h_0(z)$ is the empty log; if $s_{h_N(z)}$ is stopped then $h_{N+1}(z)=h_N(z)$, and otherwise $h_{N+1}(z)$ is $h_N(z)$ followed by the letter $a_s(z)$, $s=s_{h_N(z)}$, where $a_s(z)$ is a first heavy cell for $\mu_s$ below $S_s$ containing $z$ if one exists, and $\bot$ otherwise.
--
--   For a reward function $r(s,a)$ on states and letters, the reward accumulated along a log $h=a_1\cdots a_m$ is $\mathcal R_r(h)=\sum_{i=1}^{m}r(s_{i-1},a_i)$. The *complement reward* is $c(s,a)=-\log q(s)$ if $s$ is active and $a=\bot$, and $c(s,a)=0$ otherwise. The *continuation reward* is $\kappa(s,a)=1$ if $s$ is active, $a=\bot$ and $q(s)<\tfrac12$ (a $\bot$ attempt after which the run continues), and $\kappa(s,a)=0$ otherwise. After $N$ rounds write $A_N(z)$ for the length of $h_N(z)$ (the number of attempts made), $J_N(z)=\mathcal R_c(h_N(z))$ and $K_N(z)=\mathcal R_\kappa(h_N(z))$.
--
--   Let $n\ge1$, let $P$ be a finite measure on $\mathbb R^n$, let $Q$ be a cell such that $z\in C_Q$ for $P$-almost every $z$, and let $N\in\mathbb N$. Then:
--
--   1. $J_N$ and $K_N$ are $P$-integrable;
--   2. the expected complement and continuation rewards are bounded by multiples of the expected number of attempts:
--
--   $$
--   \int J_N\,dP\le\frac1e\int A_N\,dP,\qquad\int K_N\,dP\le\frac12\int A_N\,dP .
--   $$
--
--   Both bounds hold uniformly in the number of rounds. The first controls the reward term in the entropy budget of the truncated procedure, and the second is the input for the estimate that the expected number of attempts is at most twice one plus the expected depth.
--
--   **Formalization Note** $J_N$, $K_N$ and $A_N$ are `complementTotal P Q N`, `continuingTotal P Q N` and `truncatedAttempts P Q N` (the latter cast to a real number); $q(s)$ is `complementMass P s`, and $-\log q(s)$ is computed with `Real.log`, for which $\log0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/TruncatedBounds.lean#L45-L71

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.truncated_reward_bounds {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (complementTotal P Q N) P ∧ Integrable (continuingTotal P Q N) P ∧
    (∫ z,complementTotal P Q N z ∂P) ≤ (1/Real.exp 1)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) ∧
    (∫ z,continuingTotal P Q N z ∂P) ≤ (1/2:ℝ)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) := by sorry
