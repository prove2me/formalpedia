-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_cost_bound
-- name    : OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:59:58.60446+00:00
-- url     : https://prove2.me/theorems/b5e9bef9-bba4-4a81-9a33-84893e7f81a4
-- title:
--   Expected entropy-plus-depth cost after $N$ rounds is at most the initial divergence plus the expected complement reward
-- statement:
--   A *dyadic cell* $Q$ of $\mathbb R^n$ consists of a level $\ell(Q)\in\mathbb N$ and an index vector $k\in\{0,1,\dots,2^{\ell(Q)}-1\}^n$; its point set is the half-open box $C_Q=\prod_{a=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_a}{2^{\ell(Q)}\sqrt n},\,-\tfrac{1}{2\sqrt n}+\tfrac{k_a+1}{2^{\ell(Q)}\sqrt n}\big)$, a dyadic subcube of the cube $[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n})^n$. A cell $R$ is a *descendant* of $Q$ if $\ell(R)\ge\ell(Q)$ and $C_R\subseteq C_Q$.
--
--   For a cell $Q$, $\mathcal U_Q$ denotes the uniform law on $C_Q$ (Lebesgue measure conditioned on $C_Q$), and $\mathrm{KL}(\mu\,\|\,\nu)\in[0,\infty]$ denotes the Kullback–Leibler divergence.
--
--   For a measure $\mu$ on $\mathbb R^n$ and a cell $S$, a descendant $R$ of $S$ with $\ell(R)>\ell(S)$ is *heavy* (for $\mu$ below $S$) if $\mu(C_R)>2^{-n(\ell(R)-\ell(S))/2}$, and *first heavy* if it is heavy and no heavy cell other than $R$ itself has $R$ as a descendant. The *residual region* $\mathrm{Res}_\mu(S)$ is $C_S$ minus the union of the first heavy cells.
--
--   Given a measure $P$ on $\mathbb R^n$ and a cell $Q$, the localization procedure works with *states*: a state $s$ consists of a cell $S_s$, an event $E_s\subseteq\mathbb R^n$ and a flag saying whether $s$ is *active* or *stopped*. Write $\mu_s=P(\cdot\mid E_s)$ for the conditional law and $q(s)=\mu_s\big(\mathrm{Res}_{\mu_s}(S_s)\big)$ for the conditional mass of the residual region. A *letter* is either a cell $R$ or the symbol $\bot$, and a *log* is a finite word of letters. Reading a letter leaves a stopped state unchanged and acts on an active state $s$ as follows: the letter $R$ produces the active state with cell $R$ and event $E_s\cap C_R$ if $R$ is first heavy for $\mu_s$ below $S_s$ (and event $\varnothing$ otherwise); the letter $\bot$ keeps the cell, replaces the event by $E_s\cap\mathrm{Res}_{\mu_s}(S_s)$, and stops exactly when $q(s)\ge\tfrac12$. For a log $h=a_1\cdots a_m$ let $s_0=(Q,C_Q,\text{active})$ and let $s_i$ be obtained from $s_{i-1}$ by reading $a_i$; the state of $h$ is $s_h=s_m$, and we abbreviate $E_h=E_{s_h}$ and $S_h=S_{s_h}$.
--
--   The *run* of a point $z\in\mathbb R^n$ is defined recursively: $h_0(z)$ is the empty log; if $s_{h_N(z)}$ is stopped then $h_{N+1}(z)=h_N(z)$, and otherwise $h_{N+1}(z)$ is $h_N(z)$ followed by the letter $a_s(z)$, $s=s_{h_N(z)}$, where $a_s(z)$ is a first heavy cell for $\mu_s$ below $S_s$ containing $z$ if one exists, and $\bot$ otherwise.
--
--   For a reward function $r(s,a)$ on states and letters, the reward accumulated along a log $h=a_1\cdots a_m$ is $\mathcal R_r(h)=\sum_{i=1}^{m}r(s_{i-1},a_i)$. The *complement reward* is $c(s,a)=-\log q(s)$ if $s$ is active and $a=\bot$, and $c(s,a)=0$ otherwise. Let $J_N(z)=\mathcal R_c(h_N(z))$ be the complement reward accumulated by the run of $z$ in its first $N$ rounds, and define the *cost* of a log $h$ as
--   $$
--   \Phi(h)=\mathrm{KL}\big(P(\cdot\mid E_h)\,\big\|\,\mathcal U_{S_h}\big)+\frac{n\log2}{2}\big(\ell(S_h)-\ell(Q)\big).
--   $$
--
--   Let $n\ge1$, let $P$ be a probability measure on $\mathbb R^n$, let $Q$ be a cell with $P\ll\mathcal U_Q$ and $\mathrm{KL}(P\,\|\,\mathcal U_Q)<\infty$, and let $N\in\mathbb N$. Then:
--
--   1. the function $z\mapsto\Phi(h_N(z))$ is $P$-integrable;
--   2. its expectation satisfies
--
--   $$
--   \int\Phi\big(h_N(z)\big)\,dP(z)\;\le\;\mathrm{KL}(P\,\|\,\mathcal U_Q)+\int J_N\,dP .
--   $$
--
--   This is the main entropy estimate for the truncated procedure: the expected divergence of the conditional law on the current history from the uniform law on the current cell, plus $\frac{n\log2}{2}$ per level of depth, is at most the initial divergence plus the expected complement reward. The bounds on the expected depth, on the expected number of attempts and the final budget are all derived from it.
--
--   **Formalization Note** $\Phi(h)$ is `historyCost P Q h`, in which the divergence is converted to a real number with `toReal` (it is finite for every history of positive probability), and the level difference is a natural-number subtraction. The divergence $\mathrm{KL}(P\,\|\,\mathcal U_Q)$ on the right is likewise converted with `toReal`, and $J_N$ is `complementTotal P Q N`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/EntropyBudget.lean#L51-L79

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

theorem OAI.RepeatedLocalization.FiniteEntropy.truncated_cost_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => historyCost P Q (run P Q N z)) P ∧
    (∫ z,historyCost P Q (run P Q N z) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + ∫ z,complementTotal P Q N z ∂P := by sorry
