-- Prove2me | Theorems.Thm_OAI_RandomKSAT_sum_fin_indicator_lt
-- name    : OAI.RandomKSAT.sum_fin_indicator_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:59:08.588393+00:00
-- url     : https://prove2.me/theorems/7f96cc75-52a2-4466-a333-21dbf2a9061e
-- title:
--   Counting the indices below $N$ among $0,1,\dots,L-1$
-- statement:
--   Let $L$ and $N$ be natural numbers, and for a statement $P$ let $\mathbf 1[P]$ be $1$ if $P$ holds and $0$ otherwise.
--
--   **Theorem.** If $N\le L$, then
--   $$
--   \sum_{j=0}^{L-1}\mathbf 1[j<N]=N,
--   $$
--   where the sum is computed in $\mathbb R$.
--
--   This elementary count evaluates sums of indicators such as $\sum_{m<L}\mathbf 1[\text{the first } m \text{ clauses of a formula are satisfiable}]$: once the indicator is known to equal $\mathbf 1[m<N]$ for a threshold $N\le L$, the sum is $N$.
--
--   **Formalization Note** The index $j$ ranges over `Fin L`, and the summand is `if j.val < N then (1 : ℝ) else 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiniteVariance.lean#L151-L166

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.sum_fin_indicator_lt {L N : ℕ} (hN : N ≤ L) :
    (∑ j : Fin L, if j.val < N then (1 : ℝ) else 0) = N := by sorry
