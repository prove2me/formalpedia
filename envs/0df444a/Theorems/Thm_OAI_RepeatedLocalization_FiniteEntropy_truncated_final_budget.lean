-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_truncated_final_budget
-- name    : OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:02:27.245487+00:00
-- url     : https://prove2.me/theorems/5ff89350-9178-4cab-9c8e-479b047b0856
-- title:
--   Uniform entropy–depth budget for the truncated localization procedure when $n\ge 32$
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
--   After $N$ rounds write $D_N(z)=\ell(S_{h_N(z)})-\ell(Q)$ for the depth reached by the run of $z$, and $H_N(z)=\mathrm{KL}\big(P(\cdot\mid E_{h_N(z)})\,\|\,\mathcal U_{S_{h_N(z)}}\big)$ for the divergence of the conditional law on its current history from the uniform law on its current cell.
--
--   Let $n\ge32$, let $P$ be a probability measure on $\mathbb R^n$, let $Q$ be a cell with $P\ll\mathcal U_Q$ and $\mathrm{KL}(P\,\|\,\mathcal U_Q)<\infty$, and let $N\in\mathbb N$. Then
--
--   $$
--   \int\Big[H_N(z)+\frac{n\log2}{4}\,D_N(z)\Big]\,dP(z)\;\le\;\mathrm{KL}(P\,\|\,\mathcal U_Q)+\frac2e .
--   $$
--
--   The bound is uniform in $N$ and carries exactly the constants of the final entropy inequality of the main regularization theorem, $\frac{\log2}{4}n$ per level of depth and the additive loss $2/e$. Once almost sure termination is known it passes to the terminal quantities, and since $H_N\ge0$ it also gives a uniform bound on the expected depth, which drives the proof of almost sure termination.
--
--   **Formalization Note** The integrand is `(historyKL P Q (run P Q N z)).toReal + entropySlope n / 2 * truncatedDepth P Q N z`, where `entropySlope n` $=\frac{n\log2}{2}$, divergences are converted to real numbers with `toReal`, and the depth is a natural-number subtraction of levels cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/EntropyBudget.lean#L132-L149

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

theorem OAI.RepeatedLocalization.FiniteEntropy.truncated_final_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(historyKL P Q (run P Q N z)).toReal + entropySlope n/2*(truncatedDepth P Q N z:ℝ) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by sorry
