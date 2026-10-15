-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_terminal_regular
-- name    : OAI.RepeatedLocalization.FiniteEntropy.terminal_regular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:06:00.130141+00:00
-- url     : https://prove2.me/theorems/801dc9f9-b006-4132-af0f-7ddc7a40fb10
-- title:
--   Positive-probability terminal logs end in descendant cells with regular conditional laws of finite relative entropy
-- statement:
--   Fix a dimension $n\ge 32$ and work in $\mathbb{R}^n$ with the dyadic grid of the cube $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$. A *cell* $Q=(J,k)$ consists of a level $|Q|=J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$; its box is the half-open cube
--
--   $$
--   B_Q=\prod_{a=1}^{n}\Big[-\frac{1}{2\sqrt n}+\frac{k_a}{2^J\sqrt n},\ -\frac{1}{2\sqrt n}+\frac{k_a+1}{2^J\sqrt n}\Big).
--   $$
--
--   A cell $R$ is a *descendant* of $Q$ if $|R|\ge|Q|$ and $B_R\subseteq B_Q$. Let $U_Q$ be the uniform law on $B_Q$ (Lebesgue measure conditioned on $B_Q$), and let $D(\mu\|\nu)\in[0,\infty]$ denote the Kullback–Leibler divergence.
--
--   *Heavy cells, residual, regularity.* For a measure $\mu$ and a cell $S$, a descendant $R$ of $S$ with $|R|>|S|$ is *heavy* if $\mu(B_R)>2^{-n(|R|-|S|)/2}$, and *first heavy* if moreover no heavy cell other than $R$ itself has $R$ as a descendant. The *residual* $\mathrm{Res}(\mu,S)$ is $B_S$ minus the union of the boxes of all first heavy cells. A probability measure $\mu$ is *regular* for $S$ if $\mu(B_S)=1$ and $\mu(B_R)\le 2\cdot 2^{-n(|R|-|S|)/2}$ for every descendant $R$ of $S$ with $|R|>|S|$.
--
--   *The localization run.* Fix a probability measure $P$ on $\mathbb{R}^n$ and a starting cell $Q$. A *log* is a finite word in the letter "none" and letters "$R$" ($R$ a cell). Reading a log $h$ letter by letter from the active state $(Q,B_Q)$ produces a state $s(h)$ consisting of a current cell $T_h$, a current event $E_h$ and a flag "active" or "stopped". Stopped states never change. From an active state $(S,E)$, with $\mu=P(\cdot\mid E)$, the letter $R$ leads to the active state $(R,\,E\cap B_R)$ if $R$ is first heavy for $(\mu,S)$, and to the active state $(R,\emptyset)$ otherwise; the letter none leads to $(S,\,E\cap\mathrm{Res}(\mu,S))$, which is stopped exactly when $\mu(\mathrm{Res}(\mu,S))\ge\tfrac12$. A point $z\in\mathbb{R}^n$ generates its own log: as long as the current state $(S,E)$ is active, it appends the first heavy cell for $(P(\cdot\mid E),S)$ that contains $z$ if there is one (first heavy cells are pairwise disjoint), and the letter none otherwise. The point *terminates* if it reaches a stopped state after finitely many steps, and its *terminal log* $\tau(z)$ is its log at the first such step (the empty log if $z$ never terminates). For a log $h$, $T_h$ is called the *terminal cell* and $P_h=P(\cdot\mid\{z:\tau(z)=h\})$ the *terminal law*.
--
--   **Theorem.** Let $n\ge 32$, let $Q$ be a cell and let $P$ be a probability measure on $\mathbb{R}^n$ with $P\ll U_Q$ and $D(P\|U_Q)<\infty$. Then for every log $h$ with $P(\{z:\tau(z)=h\})>0$ the following hold.
--
--   1. The terminal cell $T_h$ is a descendant of $Q$.
--   2. The terminal law $P_h$ is regular for $T_h$.
--   3. The terminal law has finite relative entropy with respect to the uniform law on the terminal cell: $D(P_h\|U_{T_h})<\infty$.
--
--   Explicitly, claim 2 says that
--
--   $$
--   P_h\big(B_{T_h}\big)=1\qquad\text{and}\qquad P_h(B_R)\le 2\cdot 2^{-n(|R|-|T_h|)/2}\quad\text{for every descendant }R\text{ of }T_h\text{ with }|R|>|T_h|.
--   $$
--
--   This is the per-log part of the finite-entropy regularization theorem: every log of positive probability ends in a subcell of $Q$ on which the conditional law of the point gives every proper subcell at most twice the heaviness threshold. The finiteness in claim 3 is what allows the averaged entropy budget of the run to be passed between real-valued integrals and lower integrals of extended nonnegative reals.
--
--   **Formalization Note** Points are `Coordinate n`, cells are pairs `⟨J, k⟩` of type `Cell n`, logs are lists of `Option (Cell n)` with `none` as the stopping letter, and conditional measures are `ProbabilityTheory.cond`. Relative entropy is `InformationTheory.klDiv`, valued in extended nonnegative reals, so finiteness is written as inequality with $\infty$, and the positivity hypothesis is `P {z | terminalLog P Q z = h} ≠ 0`. The number of steps `attempts P Q z` is defined to be $0$ for points that never stop, which is why their terminal log is the empty word; the cell recorded at a step is selected by `Classical.choose`, which is harmless because first heavy cells containing a given point are unique.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Termination.lean#L160-L181

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
open Filter
open scoped Topology

theorem OAI.RepeatedLocalization.FiniteEntropy.terminal_regular {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P {z | terminalLog P Q z = h} ≠ 0) :
    Descendant Q (terminalCell P Q h) ∧ Regular (terminalLaw P Q h) (terminalCell P Q h) ∧
      InformationTheory.klDiv (terminalLaw P Q h) (uniformCell (terminalCell P Q h)) ≠ ∞ := by sorry
