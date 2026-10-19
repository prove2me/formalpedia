-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_two_exceptions_bound
-- name    : OAI.EntropyRateDimension.FiniteEntropy.two_exceptions_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:03:47.541293+00:00
-- url     : https://prove2.me/theorems/24e9b126-33c1-4ebf-97cd-0d68a641ee84
-- title:
--   Two of many pairwise independent events rarely occur together
-- statement:
--   Let $p\ge0$ on a finite set $s$ and $(E_i)_{i\in I}$ a finite family of events that are pairwise independent: $P(E_i\cap E_j)=P(E_i)P(E_j)$ for $i\ne j$, where $P(E)=\sum_{a\in E}p_a$. Let $t=\sum_iP(E_i)$ and let $q$ be the weight of the points in at least two of the events. Then
--   $$
--   q\le t^2\qquad\text{and}\qquad q\le t .
--   $$
--
--   The quadratic bound is the useful one when $t$ is small: two exceptional events at once are much rarer than one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L560-L605

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.two_exceptions_bound {α : Type uα} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hind : ∀ i j, i ≠ j →
      (∑ a ∈ s, if E i a ∧ E j a then p a else 0) =
        (∑ a ∈ s, if E i a then p a else 0) *
        (∑ a ∈ s, if E j a then p a else 0)) :
    let t := ∑ i, ∑ a ∈ s, if E i a then p a else 0
    let q := ∑ a ∈ s, if ∃ i j, i ≠ j ∧ E i a ∧ E j a then p a else 0
    q ≤ t ^ 2 ∧ q ≤ t := by sorry
