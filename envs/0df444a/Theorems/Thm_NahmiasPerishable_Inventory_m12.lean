-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m12
-- name    : NahmiasPerishable.Inventory.m12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:59.300261+00:00
-- url     : https://prove2.me/theorems/4d672f9e-07e6-4438-b550-9bdc971d9163
-- title:
--   Stationary outdating is convex in the critical number
-- statement:
--   Daily demand is a discrete random variable so that starting stock levels form a discrete time, discrete state space Markov chain. They prove Cohen's conjecture that expected outdating in the steady state is a convex function of the order up to level S.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - reading: expected outdating in steady state → existence of a common rate for invariant laws of the actual FIFO age kernel; reason: the objective is physical expiration under stationarity, not an arbitrary convex function; demand can have countable real support
--   - encoding: convexity as a function of S → ConvexOn on all nonnegative real critical levels; reason: no bounded grid or finite-state restriction is introduced
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(ii), Stationary outdating is convex in the critical number (unnumbered), p. 689 (PDF 10), DOI:10.1287/opre.30.4.680; review attribution: Chazan and Gal [1977].

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory Set

namespace NahmiasPerishable.Inventory

theorem m12 (μ : Measure ℝ) (hμ : DiscreteDemand μ) (k : ℕ) :
    ∃ rate : ℝ → ℝ, (∀ S, 0 ≤ S → IsStationaryRate μ k S (rate S)) ∧
      ConvexOn ℝ (Ici 0) rate := by sorry

end NahmiasPerishable.Inventory
