-- Prove2me | Theorems.Thm_Kyprianou_Ch01_nonnegativeSeriesMinWeightedBounds
-- name    : Kyprianou.Ch01.nonnegativeSeriesMinWeightedBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:54:55.827595+00:00
-- url     : https://prove2.me/theorems/ccded479-06d6-4e60-ad03-12277a1473dc
-- title:
--   Pointwise minimum bounds a bounded weighted nonnegative series by its unweighted residual mass
-- statement:
--   For two nonnegative summable real sequences a,b and fixed weights 0≤w≤1, the weighted sum of min(a,b) is below the weighted sum of a, which is below the weighted sum of min(a,b) plus the unweighted mass lost in passing from a to min(a,b). This deterministic inequality is the residual-mass component of the discrete Scheffe convergence proof and isolates the nontrivial infinite-sum comparisons from the separate Tannery limit theorem.
-- source:
--   Discrete Scheffe lemma; Kyprianou (2006), Exercise 1.11(iii)

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.nonnegativeSeriesMinWeightedBounds
    (a b w : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hasum : Summable a)
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) :
    (∑' k, min (a k) (b k) * w k) ≤
      (∑' k, a k * w k) ∧
    (∑' k, a k * w k) ≤
      (∑' k, min (a k) (b k) * w k) +
        (∑' k, a k) - (∑' k, min (a k) (b k)) := by
  sorry
