-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_event_union_bound
-- name    : OAI.EntropyRateDimension.FiniteEntropy.event_union_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:03:18.276987+00:00
-- url     : https://prove2.me/theorems/2a2d1332-76d5-4398-a859-3fb5cd096a0a
-- title:
--   Union bound for finitely many weighted events
-- statement:
--   Let $p\ge0$ be weights on a finite set $s$ and $(E_i)_{i\in I}$ a finite family of events. Then the weight of the union is at most the sum of the weights:
--   $$
--   \sum_{a\in s,\ \exists i,\ E_i(a)}p_a\ \le\ \sum_{i\in I}\ \sum_{a\in s,\ E_i(a)}p_a .
--   $$
--
--   This is the union bound for finitely supported weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L541-L558

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.event_union_bound {α : Type uα} {ι : Type uι} [Fintype ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a) :
    (∑ a ∈ s, if ∃ i, E i a then p a else 0) ≤
      ∑ i, ∑ a ∈ s, if E i a then p a else 0 := by sorry
