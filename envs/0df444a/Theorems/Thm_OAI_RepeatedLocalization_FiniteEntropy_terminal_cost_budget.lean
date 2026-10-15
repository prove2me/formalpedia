-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_terminal_cost_budget
-- name    : OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:07:05.455495+00:00
-- url     : https://prove2.me/theorems/f3666db4-c9f6-451c-84d3-683dbe3df652
-- title:
--   Terminal entropy-plus-depth cost of dyadic localization is integrable with mean at most $D(P\|U_Q)+2/e$
-- statement:
--   We use the dyadic localization run of a probability measure $P$ on $\mathbb{R}^n$ started from a cell $Q$. A cell $Q=(J,k)$ has a level $|Q|=J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$, and its box $B_Q=\prod_{a=1}^n\big[-\frac{1}{2\sqrt n}+\frac{k_a}{2^J\sqrt n},\,-\frac{1}{2\sqrt n}+\frac{k_a+1}{2^J\sqrt n}\big)$ is a half-open subcube of $\big[-\frac{1}{2\sqrt n},\frac{1}{2\sqrt n}\big)^n$. A cell $R$ is a descendant of $S$ if $|R|\ge|S|$ and $B_R\subseteq B_S$. Let $U_Q$ be the uniform law on $B_Q$ and $D(\mu\|\nu)\in[0,\infty]$ the Kullback–Leibler divergence.
--
--   The run of a point $z$ keeps a current cell $S$ and a current event $E$, starting from $(Q,B_Q)$. At each step put $\mu=P(\cdot\mid E)$; a descendant $R$ of $S$ with $|R|>|S|$ is *heavy* if $\mu(B_R)>2^{-n(|R|-|S|)/2}$ and *first heavy* if no heavy cell other than $R$ has $R$ as a descendant, and the residual $\mathrm{Res}$ is $B_S$ minus the boxes of all first heavy cells. If $z$ lies in a first heavy cell $R$, the run records $R$ and moves to $(R,E\cap B_R)$; otherwise it records the letter none, moves to $(S,E\cap\mathrm{Res})$, and stops if $\mu(\mathrm{Res})\ge\frac12$. The point terminates if the run stops after finitely many steps, and its terminal log $\tau(z)$ is the word recorded up to the stopping step (the empty word if it never stops). Since the cell, event and conditional law after a word depend only on the word, we can define the terminal cell $T(z)$ as the cell reached after reading $\tau(z)$, the terminal law $P_{\tau(z)}=P(\cdot\mid\{w:\tau(w)=\tau(z)\})$, and the depth $d(z)=|T(z)|-|Q|$.
--
--   **Theorem.** Let $n\ge 32$, let $Q$ be a cell and let $P$ be a probability measure on $\mathbb{R}^n$ with $P\ll U_Q$ and $D(P\|U_Q)<\infty$. Then the terminal cost
--   $$
--   F(z)=D\big(P_{\tau(z)}\,\big\|\,U_{T(z)}\big)+\frac{n\log 2}{4}\,d(z)
--   $$
--   is $P$-integrable, and
--   $$
--   \int_{\mathbb{R}^n}\Big(D\big(P_{\tau(z)}\,\big\|\,U_{T(z)}\big)+\frac{n\log 2}{4}\,d(z)\Big)\,dP(z)\;\le\;D(P\|U_Q)+\frac{2}{e}.
--   $$
--
--   This is the entropy budget of the localization: the average relative entropy that remains in the terminal cell, plus a price of $\frac{n\log2}{4}$ nats for every dyadic level descended, never exceeds the initial relative entropy plus the constant $2/e$. Since both summands are nonnegative, it implies that the depth and the terminal relative entropy are separately integrable, and that $\int d\,dP\le\frac{4}{n\log 2}\big(D(P\|U_Q)+\frac2e\big)$. It is a real-valued version of the final inequality of the finite-entropy regularization theorem, which is stated with extended nonnegative reals.
--
--   **Formalization Note** The coefficient is `entropySlope n / 2`, where `entropySlope n` is $\frac{n\log2}{2}$. The terminal relative entropy `terminalKL P Q z` is an extended nonnegative real converted with `ENNReal.toReal`, which sends $\infty$ to $0$; by the companion regularity result it is finite for $P$-almost every $z$, so this convention does not affect the statement. The divergence $D(P\|U_Q)$ on the right is converted the same way; it is finite by hypothesis, so nothing is lost. The depth uses truncated natural-number subtraction of levels, which equals the true level difference for $P$-almost every $z$ because terminal cells of logs of positive probability are descendants of $Q$. The integral is the Bochner integral, and integrability is part of the conclusion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/TerminalBudget.lean#L32-L56

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Definitions.Def_OAI_Probability_Localization_EntropyBudget
import Definitions.Def_OAI_Probability_Localization_TerminalBudget

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.terminal_cost_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ)) P ∧
      (∫ z,(terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ) ∂P) ≤
        (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by sorry
