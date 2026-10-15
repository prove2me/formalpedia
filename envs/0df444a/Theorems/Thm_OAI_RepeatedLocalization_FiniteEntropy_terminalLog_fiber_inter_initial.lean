-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_terminalLog_fiber_inter_initial
-- name    : OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:49:43.622447+00:00
-- url     : https://prove2.me/theorems/da663595-bd44-4169-a3d3-c8511e1d8dea
-- title:
--   Within the starting cell, the fiber of a terminal log is the terminal event
-- statement:
--   Fix a dimension $n\ge1$. A dyadic cell is a pair $c=(J,k)$ of a level $\ell(c)=J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$. Its box is $B_c=\prod_{i=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_i}{\sqrt n\,2^J},\ -\tfrac{1}{2\sqrt n}+\tfrac{k_i+1}{\sqrt n\,2^J}\big)\subseteq\mathbb{R}^n$, a dyadic subcube of $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$. For cells $c,R$ write $c\preceq R$ ($R$ is a descendant of $c$) if $\ell(c)\le\ell(R)$ and $B_R\subseteq B_c$. For a measure $\mu$ on $\mathbb{R}^n$ and a cell $c$, a cell $R$ is heavy for $(\mu,c)$ if $c\preceq R$, $\ell(c)<\ell(R)$ and $\mu(B_R)>2^{-n(\ell(R)-\ell(c))/2}$. It is first heavy for $(\mu,c)$ if moreover every cell $E$ that is heavy for $(\mu,c)$ and satisfies $E\preceq R$ equals $R$. The residual of $(\mu,c)$ is $\mathrm{Res}_\mu(c)=B_c\setminus\bigcup\{B_R:\ R\text{ first heavy for }(\mu,c)\}$.
--
--   A letter is either a cell or the symbol $\bot$ (none), and a log is a finite word of letters. The attempt letter $a^c_\mu(z)$ of a point $z\in\mathbb{R}^n$ is a first heavy cell for $(\mu,c)$ whose box contains $z$, picked by a fixed choice function, if such a cell exists, and $\bot$ otherwise. The branch of a letter is $\mathrm{Br}^c_\mu(\bot)=\mathrm{Res}_\mu(c)$, while for a cell $R$ it is $\mathrm{Br}^c_\mu(R)=B_R$ if $R$ is first heavy for $(\mu,c)$ and $\mathrm{Br}^c_\mu(R)=\varnothing$ otherwise.
--
--   Fix a measure $P$ on $\mathbb{R}^n$ and a starting cell $Q$, and write $P(\cdot\mid E)$ for $P$ conditioned on a set $E$. A state $s=(c,E,\mathrm{stop})$ consists of a current cell $c$, a current event $E\subseteq\mathbb{R}^n$ and a flag that is active or stopped. Reading a letter $a$ leaves a stopped state unchanged. An active state $(c,E,\text{active})$ becomes, with $\mu=P(\cdot\mid E)$ and $B=\mathrm{Br}^c_\mu(a)$, the state whose cell is $R$ if $a=R$ and $c$ if $a=\bot$, whose event is $E\cap B$, and which is stopped exactly when $a=\bot$ and $\mu(B)\ge\tfrac12$. For a log $h$, $\mathrm{state}(h)=(c_h,E_h,\mathrm{stop}_h)$ is obtained by reading the letters of $h$ in order, starting from $(Q,B_Q,\text{active})$.
--
--   The run of a point $z\in\mathbb{R}^n$ is the sequence of logs given by $\mathrm{run}_0(z)=\langle\rangle$ (the empty log) and, for $N\ge0$, by $\mathrm{run}_{N+1}(z)=\mathrm{run}_N(z)$ if $\mathrm{state}(\mathrm{run}_N(z))$ is stopped; otherwise $\mathrm{run}_{N+1}(z)$ is $\mathrm{run}_N(z)$ followed by the letter $a^{c}_{P(\cdot\mid E)}(z)$, where $(c,E,\cdot)=\mathrm{state}(\mathrm{run}_N(z))$. A point $z$ terminates if $\mathrm{state}(\mathrm{run}_N(z))$ is stopped for some $N$. Its number of attempts $\mathrm{att}(z)$ is the least such $N$, or $0$ if $z$ does not terminate, and its terminal log is $T(z)=\mathrm{run}_{\mathrm{att}(z)}(z)$.
--
--   Let $z\in B_Q$ be a point that terminates. Then
--
--   $$
--   B_Q\cap\{w\in\mathbb{R}^n:\ T(w)=T(z)\}=E_{T(z)} .
--   $$
--
--   So inside the starting cell, the points with the same terminal log as $z$ are exactly the points of the event of the terminal state of $z$. When $P(B_Q)=1$, the terminal law $P(\cdot\mid T=h)$ of a log $h$ realized by such a point is $P$ conditioned on $E_h$. This is how the regularity of the terminal law follows from the stopping criterion, and how its relative entropy is computed.
--
--   **Formalization Note** Cells are `Cell n`, boxes are `cellSet`, $c\preceq R$ is `Descendant c R`, letters are `Letter n = Option (Cell n)` with `none` for $\bot$, logs are lists of letters and states form the structure `State n`. In the heaviness test masses are compared as real numbers through `toReal`. The conditioned measure `ProbabilityTheory.cond P E` is the zero measure when $P(E)$ is $0$ or infinite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/History.lean#L353-L372

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.terminalLog_fiber_inter_initial {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    cellSet Q ∩ {w | terminalLog P Q w = terminalLog P Q z} =
      (state P Q (terminalLog P Q z)).event := by sorry
