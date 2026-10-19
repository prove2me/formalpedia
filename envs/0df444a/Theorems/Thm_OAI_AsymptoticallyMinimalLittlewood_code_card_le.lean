-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_code_card_le
-- name    : OAI.AsymptoticallyMinimalLittlewood.code_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:38:01.008712+00:00
-- url     : https://prove2.me/theorems/9d1b0fe1-ac0b-4d6c-974b-2305d71984e0
-- title:
--   Counting integer vectors of bounded $\ell^1$ norm
-- statement:
--   Let $I$ be a finite set with $m=|I|$ elements and let $C$ be a finite set of integer vectors $c\colon I\to\mathbb{Z}$. Let $a,M$ be real numbers with $a\ge0$ and $e^{-a}\le\tfrac12$, and assume that every $c\in C$ satisfies $\sum_{i\in I}|c_i|\le M$. Then
--
--   $$
--   |C|\le\exp\big(aM+4m\,e^{-a}\big).
--   $$
--
--   Thus a set of integer codes with total cost at most $M$ is at most exponentially large in $aM+4me^{-a}$; choosing $a$ of logarithmic size balances the two terms and gives an entropy-type count. In the partial-coloring argument this bounds the number of distinct rounding patterns of the row sums.
--
--   **Formalization Note** The hypothesis $a\ge0$ already follows from $e^{-a}\le\tfrac12$, but it is stated separately in Lean.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L191-L209

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.code_card_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2) (hM : ∀ c ∈ C, (∑ i, |(c i : ℝ)|) ≤ M) :
    (C.card : ℝ) ≤ Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a)) := by sorry
