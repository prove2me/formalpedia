-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_attempts_integral
-- name    : OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:00:52.565991+00:00
-- url     : https://prove2.me/theorems/0c19ea37-279c-44dd-94a9-7ede86d41551
-- title:
--   Expected number of attempts is at most twice one plus the expected depth
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
--   After $N$ rounds write $A_N(z)$ for the length of $h_N(z)$ (the number of attempts made by the run of $z$) and $D_N(z)=\ell(S_{h_N(z)})-\ell(Q)$ for the depth it has reached.
--
--   Let $n\ge1$, let $P$ be a probability measure on $\mathbb R^n$, let $Q$ be a cell with $P\ll\mathcal U_Q$ and $\mathrm{KL}(P\,\|\,\mathcal U_Q)<\infty$, and let $N\in\mathbb N$. Then
--
--   $$
--   \int A_N\,dP\;\le\;2\Big(1+\int D_N\,dP\Big).
--   $$
--
--   The expected number of attempts in the first $N$ rounds is thus controlled by the expected depth, uniformly in $N$. Combined with the fact that truncated depths never exceed the terminal depth, it yields the clause of the main regularization theorem stating that the expected number of attempts is at most $2(1+\text{expected depth})$; it is also a step in the uniform bound on attempts that proves almost sure termination.
--
--   **Formalization Note** $A_N$ and $D_N$ are `truncatedAttempts P Q N` and `truncatedDepth P Q N` (the latter a natural-number subtraction of levels), cast to real numbers; the integrals are Bochner integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/EntropyBudget.lean#L105-L123

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

theorem OAI.RepeatedLocalization.FiniteEntropy.truncated_attempts_integral {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(truncatedAttempts P Q N z:ℝ) ∂P) ≤ 2*(1+∫ z,(truncatedDepth P Q N z:ℝ) ∂P) := by sorry
