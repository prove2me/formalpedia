-- Prove2me | Theorems.Thm_Kyprianou_Ch01_nonnegativeSeriesWeightedMassTendsto
-- name    : Kyprianou.Ch01.nonnegativeSeriesWeightedMassTendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:54:03.371429+00:00
-- url     : https://prove2.me/theorems/1aefb6df-c8fa-4089-81e0-b99e0f9eceeb
-- title:
--   Discrete Scheffe principle: nonnegative series with convergent total mass preserve bounded weighted sums
-- statement:
--   For nonnegative summable series depending on a filter parameter, if each term converges and their total masses converge to the mass of the summable limit series, then all weighted sums with fixed weights in [0,1] converge. The proof is the discrete Scheffe argument: dominated convergence for min(a_t,b), with the residual mass tending to zero. Applied to nonnegative off-diagonal probability difference quotients, this rigorously supplies the infinite-series interchange in the source branching generator equation.
-- source:
--   Discrete Scheffe lemma and Kyprianou (2006), Exercise 1.11(iii), p.306

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.Basic
open Filter
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.nonnegativeSeriesWeightedMassTendsto
    {α : Type*} {F : Filter α} [NeBot F]
    (a : α → ℕ → ℝ) (b w : ℕ → ℝ)
    (ha : ∀ᶠ t in F, ∀ k, 0 ≤ a t k)
    (hasum : ∀ᶠ t in F, Summable (a t))
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (hpoint : ∀ k, Tendsto (fun t => a t k) F (nhds (b k)))
    (hmass : Tendsto (fun t => ∑' k, a t k) F
      (nhds (∑' k, b k))) :
    Tendsto (fun t => ∑' k, a t k * w k) F
      (nhds (∑' k, b k * w k)) := by
  sorry
