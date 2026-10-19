-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_no_large_coordinate
-- name    : OAI.EntropyRateDimension.FiniteEntropy.no_large_coordinate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:04:21.567545+00:00
-- url     : https://prove2.me/theorems/2104c28e-27f6-49ca-a73d-8fa769e4e45b
-- title:
--   A small sum with one large term forces two large terms
-- statement:
--   Let $x_i$ be real numbers indexed by a finite set $I$ of size $k$, and let $a>0$. Suppose $|\sum_ix_i|<a/2$, and that no two distinct indices have $|x_i|,|x_j|\ge a/(4k)$. Then every coordinate is small:
--   $$
--   |x_i|<a\qquad\text{for all }i\in I .
--   $$
--
--   Equivalently, if some coordinate is at least $a$ while the sum is below $a/2$, then two coordinates are at least $a/(4k)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L607-L640

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.no_large_coordinate {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hE : ¬∃ i j, i ≠ j ∧ a / (4 * Fintype.card ι) ≤ |x i| ∧
      a / (4 * Fintype.card ι) ≤ |x j|)
    (hB : |∑ i, x i| < a / 2) (i : ι) : |x i| < a := by sorry
