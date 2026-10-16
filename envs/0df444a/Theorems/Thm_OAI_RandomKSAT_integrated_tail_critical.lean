-- Prove2me | Theorems.Thm_OAI_RandomKSAT_integrated_tail_critical
-- name    : OAI.RandomKSAT.integrated_tail_critical
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:01:22.117292+00:00
-- url     : https://prove2.me/theorems/f7f1d287-ad60-4c8b-892e-a0d9f7d01c7e
-- title:
--   A nonincreasing function bounded by $\min(L,A/a)$ has integral at most $A(1+\log L)$ over $[0,1]$
-- statement:
--   Let $F:\mathbb R\to\mathbb R$ be a function and $A,L$ real numbers.
--
--   **Theorem.** Assume that $F$ is nonincreasing, that $A\ge1$ and $L\ge1$, that $F(a)\le L$ for every $a\in\mathbb R$, and that $F(a)\le A/a$ for every $a\in(0,1)$. Then
--   $$
--   \int_0^1F(a)\,da\le A\,(1+\log L),
--   $$
--   where $\log$ is the natural logarithm.
--
--   The bound $A/a$ on its own is not integrable at $0$; combined with the uniform bound $L$ it costs only a logarithmic factor. The lemma is used in layer-cake arguments: a reward with values in $[0,1]$ is written as $\int_0^1\mathbf 1[a\le f]\,da$, the cumulative effect $F(a)$ of the level-$a$ indicator is bounded by $A/a$ and trivially by $L$, and the theorem converts these level bounds into a logarithmic bound for the reward itself.
--
--   **Formalization Note** The integral is the interval integral `∫ a in (0 : ℝ)..1, F a`; integrability is automatic because $F$ is monotone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/OccupationBounds.lean#L28-L62

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

theorem OAI.RandomKSAT.integrated_tail_critical {F : ℝ → ℝ} (hF : Antitone F)
    {A L : ℝ} (hA : 1 ≤ A) (hL : 1 ≤ L)
    (hmass : ∀ a, F a ≤ L)
    (hbound : ∀ a ∈ Set.Ioo (0 : ℝ) 1, F a ≤ A/a) :
    (∫ a in (0 : ℝ)..1, F a) ≤ A * (1+Real.log L) := by sorry
