-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_attempts_path
-- name    : OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:57:53.924706+00:00
-- url     : https://prove2.me/theorems/acc8c72b-08cd-4bbb-ab5a-06978b8f3ff5
-- title:
--   Pathwise bound on the number of attempts by depth, continuations and the stopping step
-- statement:
--   A *dyadic cell* $Q$ of $\mathbb R^n$ consists of a level $\ell(Q)\in\mathbb N$ and an index vector $k\in\{0,1,\dots,2^{\ell(Q)}-1\}^n$; its point set is the half-open box $C_Q=\prod_{a=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_a}{2^{\ell(Q)}\sqrt n},\,-\tfrac{1}{2\sqrt n}+\tfrac{k_a+1}{2^{\ell(Q)}\sqrt n}\big)$, a dyadic subcube of the cube $[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n})^n$. A cell $R$ is a *descendant* of $Q$ if $\ell(R)\ge\ell(Q)$ and $C_R\subseteq C_Q$.
--
--   For a measure $\mu$ on $\mathbb R^n$ and a cell $S$, a descendant $R$ of $S$ with $\ell(R)>\ell(S)$ is *heavy* (for $\mu$ below $S$) if $\mu(C_R)>2^{-n(\ell(R)-\ell(S))/2}$, and *first heavy* if it is heavy and no heavy cell other than $R$ itself has $R$ as a descendant. The *residual region* $\mathrm{Res}_\mu(S)$ is $C_S$ minus the union of the first heavy cells.
--
--   Given a measure $P$ on $\mathbb R^n$ and a cell $Q$, the localization procedure works with *states*: a state $s$ consists of a cell $S_s$, an event $E_s\subseteq\mathbb R^n$ and a flag saying whether $s$ is *active* or *stopped*. Write $\mu_s=P(\cdot\mid E_s)$ for the conditional law and $q(s)=\mu_s\big(\mathrm{Res}_{\mu_s}(S_s)\big)$ for the conditional mass of the residual region. A *letter* is either a cell $R$ or the symbol $\bot$, and a *log* is a finite word of letters. Reading a letter leaves a stopped state unchanged and acts on an active state $s$ as follows: the letter $R$ produces the active state with cell $R$ and event $E_s\cap C_R$ if $R$ is first heavy for $\mu_s$ below $S_s$ (and event $\varnothing$ otherwise); the letter $\bot$ keeps the cell, replaces the event by $E_s\cap\mathrm{Res}_{\mu_s}(S_s)$, and stops exactly when $q(s)\ge\tfrac12$. For a log $h=a_1\cdots a_m$ let $s_0=(Q,C_Q,\text{active})$ and let $s_i$ be obtained from $s_{i-1}$ by reading $a_i$; the state of $h$ is $s_h=s_m$, and we abbreviate $E_h=E_{s_h}$ and $S_h=S_{s_h}$.
--
--   The *run* of a point $z\in\mathbb R^n$ is defined recursively: $h_0(z)$ is the empty log; if $s_{h_N(z)}$ is stopped then $h_{N+1}(z)=h_N(z)$, and otherwise $h_{N+1}(z)$ is $h_N(z)$ followed by the letter $a_s(z)$, $s=s_{h_N(z)}$, where $a_s(z)$ is a first heavy cell for $\mu_s$ below $S_s$ containing $z$ if one exists, and $\bot$ otherwise.
--
--   For a reward function $r(s,a)$ on states and letters, the reward accumulated along a log $h=a_1\cdots a_m$ is $\mathcal R_r(h)=\sum_{i=1}^{m}r(s_{i-1},a_i)$. The *continuation reward* is $\kappa(s,a)=1$ if $s$ is active, $a=\bot$ and $q(s)<\tfrac12$ (a $\bot$ attempt after which the run continues), and $\kappa(s,a)=0$ otherwise. For a point $z$ write $A_N(z)$ for the length of $h_N(z)$ (the number of attempts in the first $N$ rounds), $D_N(z)=\ell(S_{h_N(z)})-\ell(Q)$ for the depth reached, and $K_N(z)=\mathcal R_\kappa(h_N(z))$ for the number of continuing $\bot$ attempts.
--
--   Let $n\ge1$, let $P$ be any measure on $\mathbb R^n$, let $Q$ be a cell, let $N\in\mathbb N$ and let $z\in C_Q$. Then
--
--   $$
--   A_N(z)\;\le\;D_N(z)+K_N(z)+\mathbf 1\{s_{h_N(z)}\text{ is stopped}\}.
--   $$
--
--   This deterministic inequality accounts for every attempt of a run: the number of attempts is bounded by the number of dyadic levels descended, the number of $\bot$ attempts after which the run continued, and one final stopping attempt. Integrated over $z$ and combined with $\int K_N\,dP\le\frac12\int A_N\,dP$, it yields the bound $\int A_N\,dP\le2\big(1+\int D_N\,dP\big)$ on the expected number of attempts.
--
--   **Formalization Note** $A_N$, $D_N$ and $K_N$ are `truncatedAttempts P Q N z`, `truncatedDepth P Q N z` (a natural-number subtraction of levels) and `continuingTotal P Q N z`, all cast to real numbers, and the indicator is `if (state P Q (run P Q N z)).stopped then 1 else 0`. No finiteness of $P$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/TruncatedBounds.lean#L73-L128

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

theorem OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_path {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    (truncatedAttempts P Q N z : ℝ) ≤ truncatedDepth P Q N z + continuingTotal P Q N z +
      (if (state P Q (run P Q N z)).stopped then (1:ℝ) else 0) := by sorry
