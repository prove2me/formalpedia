-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_event_subset_cell
-- name    : OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:44:21.977214+00:00
-- url     : https://prove2.me/theorems/ecf1ac04-a5d3-4329-8460-fc28a307cf4c
-- title:
--   The event of a localization state lies in the box of its current cell
-- statement:
--   Fix a dimension $n\in\mathbb{N}$. A dyadic cell is a pair $c=(J,k)$ of a level $\ell(c)=J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$. Its box is $B_c=\prod_{i=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_i}{\sqrt n\,2^J},\ -\tfrac{1}{2\sqrt n}+\tfrac{k_i+1}{\sqrt n\,2^J}\big)\subseteq\mathbb{R}^n$, a dyadic subcube of $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$. For cells $c,R$ write $c\preceq R$ ($R$ is a descendant of $c$) if $\ell(c)\le\ell(R)$ and $B_R\subseteq B_c$. For a measure $\mu$ on $\mathbb{R}^n$ and a cell $c$, a cell $R$ is heavy for $(\mu,c)$ if $c\preceq R$, $\ell(c)<\ell(R)$ and $\mu(B_R)>2^{-n(\ell(R)-\ell(c))/2}$. It is first heavy for $(\mu,c)$ if moreover every cell $E$ that is heavy for $(\mu,c)$ and satisfies $E\preceq R$ equals $R$. The residual of $(\mu,c)$ is $\mathrm{Res}_\mu(c)=B_c\setminus\bigcup\{B_R:\ R\text{ first heavy for }(\mu,c)\}$.
--
--   A letter is either a cell or the symbol $\bot$ (none), and a log is a finite word of letters. The attempt letter $a^c_\mu(z)$ of a point $z\in\mathbb{R}^n$ is a first heavy cell for $(\mu,c)$ whose box contains $z$, picked by a fixed choice function, if such a cell exists, and $\bot$ otherwise. The branch of a letter is $\mathrm{Br}^c_\mu(\bot)=\mathrm{Res}_\mu(c)$, while for a cell $R$ it is $\mathrm{Br}^c_\mu(R)=B_R$ if $R$ is first heavy for $(\mu,c)$ and $\mathrm{Br}^c_\mu(R)=\varnothing$ otherwise.
--
--   Fix a measure $P$ on $\mathbb{R}^n$ and a starting cell $Q$, and write $P(\cdot\mid E)$ for $P$ conditioned on a set $E$. A state $s=(c,E,\mathrm{stop})$ consists of a current cell $c$, a current event $E\subseteq\mathbb{R}^n$ and a flag that is active or stopped. Reading a letter $a$ leaves a stopped state unchanged. An active state $(c,E,\text{active})$ becomes, with $\mu=P(\cdot\mid E)$ and $B=\mathrm{Br}^c_\mu(a)$, the state whose cell is $R$ if $a=R$ and $c$ if $a=\bot$, whose event is $E\cap B$, and which is stopped exactly when $a=\bot$ and $\mu(B)\ge\tfrac12$. For a log $h$, $\mathrm{state}(h)=(c_h,E_h,\mathrm{stop}_h)$ is obtained by reading the letters of $h$ in order, starting from $(Q,B_Q,\text{active})$.
--
--   Then for every log $h$,
--
--   $$
--   E_h\subseteq B_{c_h}.
--   $$
--
--   So the procedure only keeps points inside the box of its current cell. This invariant ensures that the attempt letter of every surviving point is computed relative to a cell that contains the point, which is needed to identify the fibers of the run with the events of states.
--
--   **Formalization Note** Cells are `Cell n`, boxes are `cellSet`, $c\preceq R$ is `Descendant c R`, letters are `Letter n = Option (Cell n)` with `none` for $\bot$, logs are lists of letters and states form the structure `State n`. In the heaviness test masses are compared as real numbers through `toReal`. The conditioned measure `ProbabilityTheory.cond P E` is the zero measure when $P(E)$ is $0$ or infinite. The statement holds for every $n$ and every measure $P$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/History.lean#L97-L114

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.state_event_subset_cell {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    (state P Q h).event ⊆ cellSet (state P Q h).cell := by sorry
