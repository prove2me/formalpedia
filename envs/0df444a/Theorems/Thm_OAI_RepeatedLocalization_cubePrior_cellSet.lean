-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_cubePrior_cellSet
-- name    : OAI.RepeatedLocalization.cubePrior_cellSet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:41:30.20098+00:00
-- url     : https://prove2.me/theorems/ff8b04f5-9ede-44ce-bea3-6145e3987365
-- title:
--   The cube prior gives mass $2^{-nJ}$ to every dyadic cell of level $J$
-- statement:
--   Let $n\ge1$, let $C_n=\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$ and let $\lambda$ be Lebesgue measure on $\mathbb{R}^n$. The cube prior is the uniform distribution on $C_n$, defined for Borel sets $A\subseteq\mathbb{R}^n$ by
--
--   $$\Pi_n(A)=\frac{\lambda(A\cap C_n)}{\lambda(C_n)}.$$
--
--   A dyadic cell is a pair $Q=(J,k)$ of a level $J\in\mathbb{N}$ and an index vector $k\in\{0,\dots,2^J-1\}^n$, with box $B_Q=\prod_{i=1}^n\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_i}{\sqrt n\,2^J},\,-\tfrac{1}{2\sqrt n}+\tfrac{k_i+1}{\sqrt n\,2^J}\big)$. Then for every dyadic cell $Q=(J,k)$,
--
--   $$
--   \Pi_n(B_Q)=\Big(\frac12\Big)^{nJ}.
--   $$
--
--   Each cell of level $J$ is one of the $2^{nJ}$ congruent subcubes of $C_n$, and the identity makes this quantitative. It yields the masses of the uniform laws on cells: if $R=(J',k')$ is a cell with $J'\ge J$ and $B_R\subseteq B_Q$, the uniform law on $B_Q$ gives $B_R$ mass $2^{-n(J'-J)}$. This is how depth in the dyadic tree is converted into relative entropy in the entropy budget of the localization procedure.
--
--   **Formalization Note** The prior is `cubePrior n`, defined as `ProbabilityTheory.cond volume (initialCube n)`. The identity is stated in the extended nonnegative reals, with right-hand side `ENNReal.ofReal ((1/2)^(n * J))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Cells.lean#L52-L65

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells

open OAI OAI.RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.cubePrior_cellSet {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cubePrior n (cellSet Q) = ENNReal.ofReal ((1 / 2 : ℝ)^(n * Q.1)) := by sorry
