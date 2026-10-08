-- Prove2me | Theorems.Thm_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le
-- name    : OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:35:44.174477+00:00
-- url     : https://prove2.me/theorems/84999320-3725-4c17-b1cb-428d9f92f6cc
-- title:
--   A lower bound for a nonnegative weighted sum from a low-weight count
-- statement:
--   Let $R$ be a finite set of indices, let $w$ assign a real weight to each index, and let $c,\eta\in\mathbb R$. Assume $c\ge 0$ and $w(i)\ge 0$ for every $i\in R$. If the number of indices with weight at most $c$ satisfies $$\#\{i\in R:w(i)\le c\}\le\eta\,\#R,$$ then $$c(1-\eta)\,\#R\le\sum_{i\in R}w(i).$$ No separate restriction on $\eta$ is required. This finite counting estimate turns an upper bound on the number of low-weight indices into a lower bound for the total weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/CollisionCombinatorics.lean#L137-L154

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix

section


namespace OAI

open scoped BigOperators

namespace PiExponent.Collision





















theorem cutoff_mul_high_count_le_sum {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) (cutoff : ℝ)
    (hnonneg : ∀ i ∈ rows, 0 ≤ weight i) :
    cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) ≤
      ∑ i ∈ rows, weight i := by
  classical
  calc
    _ = ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), cutoff := by
      simp [mul_comm]
    _ ≤ ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ rows, weight i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ rows)
      intro i hi _
      exact hnonneg i hi



end PiExponent.Collision

end OAI

end

open scoped BigOperators

theorem OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) {cutoff η : ℝ}
    (hcutoff : 0 ≤ cutoff) (hnonneg : ∀ i ∈ rows, 0 ≤ weight i)
    (hlow : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) ≤
      η * rows.card) :
    cutoff * (1 - η) * rows.card ≤ ∑ i ∈ rows, weight i := by sorry
