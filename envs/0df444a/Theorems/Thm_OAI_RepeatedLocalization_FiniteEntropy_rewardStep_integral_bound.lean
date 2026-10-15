-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_rewardStep_integral_bound
-- name    : OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:56:33.466951+00:00
-- url     : https://prove2.me/theorems/b92e59ab-2580-4ed6-aef4-fdec4be845c7
-- title:
--   Expected reward of the next localization attempt is controlled by the probability of being active
-- statement:
--   A *dyadic cell* $Q$ of $\mathbb R^n$ consists of a level $\ell(Q)\in\mathbb N$ and an index vector $k\in\{0,1,\dots,2^{\ell(Q)}-1\}^n$; its point set is the half-open box $C_Q=\prod_{a=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_a}{2^{\ell(Q)}\sqrt n},\,-\tfrac{1}{2\sqrt n}+\tfrac{k_a+1}{2^{\ell(Q)}\sqrt n}\big)$, a dyadic subcube of the cube $[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n})^n$. A cell $R$ is a *descendant* of $Q$ if $\ell(R)\ge\ell(Q)$ and $C_R\subseteq C_Q$.
--
--   For a measure $\mu$ on $\mathbb R^n$ and a cell $S$, a descendant $R$ of $S$ with $\ell(R)>\ell(S)$ is *heavy* (for $\mu$ below $S$) if $\mu(C_R)>2^{-n(\ell(R)-\ell(S))/2}$, and *first heavy* if it is heavy and no heavy cell other than $R$ itself has $R$ as a descendant. The *residual region* $\mathrm{Res}_\mu(S)$ is $C_S$ minus the union of the first heavy cells.
--
--   Given a measure $P$ on $\mathbb R^n$ and a cell $Q$, the localization procedure works with *states*: a state $s$ consists of a cell $S_s$, an event $E_s\subseteq\mathbb R^n$ and a flag saying whether $s$ is *active* or *stopped*. Write $\mu_s=P(\cdot\mid E_s)$ for the conditional law and $q(s)=\mu_s\big(\mathrm{Res}_{\mu_s}(S_s)\big)$ for the conditional mass of the residual region. A *letter* is either a cell $R$ or the symbol $\bot$, and a *log* is a finite word of letters. Reading a letter leaves a stopped state unchanged and acts on an active state $s$ as follows: the letter $R$ produces the active state with cell $R$ and event $E_s\cap C_R$ if $R$ is first heavy for $\mu_s$ below $S_s$ (and event $\varnothing$ otherwise); the letter $\bot$ keeps the cell, replaces the event by $E_s\cap\mathrm{Res}_{\mu_s}(S_s)$, and stops exactly when $q(s)\ge\tfrac12$. For a log $h=a_1\cdots a_m$ let $s_0=(Q,C_Q,\text{active})$ and let $s_i$ be obtained from $s_{i-1}$ by reading $a_i$; the state of $h$ is $s_h=s_m$, and we abbreviate $E_h=E_{s_h}$ and $S_h=S_{s_h}$.
--
--   The *run* of a point $z\in\mathbb R^n$ is defined recursively: $h_0(z)$ is the empty log; if $s_{h_N(z)}$ is stopped then $h_{N+1}(z)=h_N(z)$, and otherwise $h_{N+1}(z)$ is $h_N(z)$ followed by the letter $a_s(z)$, $s=s_{h_N(z)}$, where $a_s(z)$ is a first heavy cell for $\mu_s$ below $S_s$ containing $z$ if one exists, and $\bot$ otherwise.
--
--   Let $n\ge1$, let $P$ be a finite measure on $\mathbb R^n$ and let $Q$ be a cell such that $z\in C_Q$ for $P$-almost every $z$. Let $r$ be a real-valued reward function on pairs (state, letter) with $r(s,a)\ge0$ for all $s,a$ and $r(s,R)=0$ for every state $s$ and every cell letter $R$, so that only the letter $\bot$ can be rewarded. Let $b\in\mathbb R$ satisfy, for every state $s$,
--   $$
--   q(s)\,r(s,\bot)\le\begin{cases}b, & s\text{ active},\\ 0, & s\text{ stopped}.\end{cases}
--   $$
--   For $N\in\mathbb N$ let $X_N(z)=r\big(s,a_s(z)\big)$ with $s=s_{h_N(z)}$ be the reward of the next attempt after $N$ rounds. Then $X_N$ is $P$-integrable and
--
--   $$
--   \int X_N\,dP\;\le\;b\int\mathbf 1\{s_{h_N(z)}\text{ is active}\}\,dP(z)=b\,P\big(\{z:\ s_{h_N(z)}\text{ is active}\}\big).
--   $$
--
--   Since $q(s)\,r(s,\bot)$ is the expected reward of an attempt made from $s$, the theorem turns a pointwise bound on this quantity into a bound on the expected reward of a round, proportional to the probability that the run is still active. It is applied to the complement reward ($-\log q(s)$ at a $\bot$ letter) with $b=1/e$ and to the continuation reward (the indicator that $\bot$ is read while $q(s)<\tfrac12$) with $b=\tfrac12$.
--
--   **Formalization Note** $X_N$ is `rewardStep P Q r N`, which is evaluated also when $s_{h_N(z)}$ is stopped, and the indicator is `activeIndicator P Q N`. The hypothesis on $b$ is required for every state, that is, every triple of a cell, a subset of $\mathbb R^n$ and a flag; $q(s)$ is `complementMass P s`, which is $0$ when $P(E_s)=0$ because conditioning on a null set gives the zero measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/RewardBounds.lean#L114-L134

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

theorem OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q)
    (r : State n → Letter n → ℝ) (hr0 : ∀ s a,0 ≤ r s a)
    (hr : ∀ s R,r s (some R) = 0) (b : ℝ)
    (hb : ∀ s, complementMass P s * r s none ≤ b*(if s.stopped then 0 else 1)) (N : ℕ) :
    Integrable (rewardStep P Q r N) P ∧
      (∫ z,rewardStep P Q r N z ∂P) ≤ b*(∫ z,activeIndicator P Q N z ∂P) := by sorry
