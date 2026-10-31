-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m02
-- name    : NahmiasPerishable.Inventory.m02
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:09.054908+00:00
-- url     : https://prove2.me/theorems/3fdad05f-48cc-4569-8c5e-b68d1d4b51c3
-- title:
--   One-period lifetime separates into newsvendor problems
-- statement:
--   If the lifetime is exactly one period, the ordering decisions in successive periods are independent and the problem reduces to a sequence of simple newsboy problems (see Arrow et al. [1958]).
--
--   Differences from the source:
--   - reading: successive one-period newsvendor decisions → inventory-position newsvendor targets, with a discounted next-period purchase charge on backlogs when another period remains; reason: only unfilled obligations carry over; physical stock expires, and the final period has zero terminal value
--   - encoding: expected costs and minimization → EReal infima, signed extended expectations, and an explicit definedness predicate; reason: undefined infinity minus infinity and nonmeasurable expectations are excluded; finite costs agree with ordinary expectations, while attainment is asserted in the conclusion
--   - encoding: an optimal policy → existence of a family of actual Bellman minimizers; reason: ties are resolved by the existential selector, without assuming uniqueness or supplying the desired regularity as a hypothesis
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2, One-period lifetime separates into newsvendor problems (unnumbered), p. 682 (PDF 3), DOI:10.1287/opre.30.4.680; review attribution: Arrow, Karlin and Scarf [1958].

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory Set

namespace NahmiasPerishable.Inventory

theorem m02 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ d ∂μ, 0 ≤ d) (b : Bool) (c h p theta alpha : ℝ)
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hp : 0 ≤ p) (htheta : 0 ≤ theta)
    (halpha : 0 < alpha ∧ alpha < 1)
    (hdefined : (singlePeriodControl μ b c h p theta alpha).defined {x | x ≤ 0 ∧ (b = false → x = 0)}) :
    ∃ z : ℕ → ℝ,
      (∀ j, 0 ≤ z j ∧ ∀ w, 0 ≤ w →
        singlePeriodNews μ b c h p theta alpha (decide (0 < j)) (z j) ≤
        singlePeriodNews μ b c h p theta alpha (decide (0 < j)) w) ∧
      (∀ n x, x ≤ 0 → (b = false → x = 0) →
        (singlePeriodControl μ b c h p theta alpha).optimal n x (z n-x)) ∧
      (∀ n x, 0 < n → x ≤ 0 → (b = false → x = 0) →
        (singlePeriodControl μ b c h p theta alpha).value n x = (-c*x : ℝ) +
          ∑ t ∈ Finset.range n, ((alpha^t : ℝ) : EReal) *
            singlePeriodNews μ b c h p theta alpha (decide (t+1 < n)) (z (n-1-t))) := by sorry

end NahmiasPerishable.Inventory
