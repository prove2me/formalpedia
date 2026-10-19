-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_code_exp_sum_le
-- name    : OAI.AsymptoticallyMinimalLittlewood.code_exp_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:37:21.834588+00:00
-- url     : https://prove2.me/theorems/f94f00ee-37ae-434f-a4e3-1d43057b6c07
-- title:
--   Partition-function bound for finite families of integer vectors
-- statement:
--   Let $I$ be a finite set with $m=|I|$ elements, let $C$ be a finite set of integer vectors $c\colon I\to\mathbb{Z}$, and let $a$ be a real number with $e^{-a}\le\tfrac12$. Then
--
--   $$
--   \sum_{c\in C}\exp\Big(-a\sum_{i\in I}|c_i|\Big)\le\exp\big(4m\,e^{-a}\big).
--   $$
--
--   The right-hand side does not depend on $C$: the weights $e^{-a\|c\|_1}$ have total mass at most $e^{4me^{-a}}$ over all of $\mathbb{Z}^I$. This is the partition function used in the entropy (counting) step of the partial-coloring method, where $c$ records the rounded values of the $m$ row sums.
--
--   **Formalization Note** The index set is a `Fintype` $\beta$ and $m$ is `Fintype.card β`; the integers $c_i$ are cast to $\mathbb{R}$ before taking absolute values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L165-L189

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.code_exp_sum_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ c ∈ C, Real.exp (-a * ∑ i, |(c i : ℝ)|)) ≤
      Real.exp (4 * Fintype.card β * Real.exp (-a)) := by sorry
