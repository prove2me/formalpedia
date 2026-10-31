-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m18
-- name    : NahmiasPerishable.Inventory.m18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:50.791268+00:00
-- url     : https://prove2.me/theorems/228afad0-984d-4ffa-829f-159c6b005833
-- title:
--   One-period FIFO rotation allocation
-- statement:
--   Assuming demands are satisfied on a FIFO basis, the one period solution which minimizes expected shortage and outdate costs involves a two-stage allocation procedure: (1) first allocate those units which are scheduled to outdate in the current planning period so as to equalize the probability that a unit outdates among the warehouses, and (2) allocate all remaining stock so as to equalize the probability of shortage at any warehouse.
--
--   Differences from the source:
--   - reading: equalize outdating and shortage probabilities across warehouses → common marginal levels lying between the left and right CDF values, with complementary inequalities at zero allocations; reason: for continuous demand and positive allocations these are the printed equalities; atoms and zero budgets require one-sided marginal conditions, not an added density or positivity assumption
--   - encoding: one-period allocations of the given old and younger stock → nonnegative real vectors with separate fixed budgets and simultaneous minimization of expected shortage and outdating; reason: only marginal demand laws enter these expectations; no independence between warehouses is required
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.e, One-period FIFO rotation allocation (unnumbered), p. 696 (PDF 17), DOI:10.1287/opre.30.4.680; review attribution: Prastacos [1978]; Yen [1965].

import Definitions.Def_NahmiasPerishable_Inventory_AllocationSurvival

open MeasureTheory Set

namespace NahmiasPerishable.Inventory

theorem m18 (n : ℕ) (hn : 0 < n) (μ : Fin n → Measure ℝ)
    (hprob : ∀ i, IsProbabilityMeasure (μ i)) (hnonneg : ∀ i, ∀ᵐ d ∂μ i, 0 ≤ d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ a b : Fin n → ℝ, Allocation A B a b ∧
      (∃ oldLevel newLevel : ℝ,
        0 ≤ oldLevel ∧ oldLevel ≤ 1 ∧ 0 ≤ newLevel ∧ newLevel ≤ 1 ∧
        (∀ i, oldLevel ≤ cdf (μ i) (a i) ∧
          (0 < a i → ((μ i) (Iio (a i))).toReal ≤ oldLevel)) ∧
        (∀ i, 1-cdf (μ i) (a i+b i) ≤ newLevel ∧
          (0 < b i → newLevel ≤ 1-((μ i) (Iio (a i+b i))).toReal))) ∧
      (∀ u v : Fin n → ℝ, Allocation A B u v →
        allocationOutdate μ a ≤ allocationOutdate μ u ∧
        allocationShortage μ a b ≤ allocationShortage μ u v) := by sorry

end NahmiasPerishable.Inventory
