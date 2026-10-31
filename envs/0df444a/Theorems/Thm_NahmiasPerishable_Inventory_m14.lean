-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m14
-- name    : NahmiasPerishable.Inventory.m14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:28:11.206027+00:00
-- url     : https://prove2.me/theorems/531295a6-1275-4585-9046-3fcbc7d5cc03
-- title:
--   Small-demand stationary outdating
-- statement:
--   An interesting observation made by Chazan and Gal is that if demand in a period, D, is less than or equal to S/m with probability 1, then the expected outdating per period will eventually be S/m − E(D).
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - reading: eventually expected outdating per period equals S/m−E(D) → the common stationary expected rate equals that expression; reason: the surrounding paragraph concerns steady-state means, not eventual equality of every sample-path age coordinate
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(ii), Small-demand stationary outdating (unnumbered), p. 689 (PDF 10), DOI:10.1287/opre.30.4.680; review attribution: Chazan and Gal [1977].

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory

namespace NahmiasPerishable.Inventory

theorem m14 (μ : Measure ℝ) (hμ : DiscreteDemand μ) (k : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (hsmall : ∀ᵐ d ∂μ, d ≤ S/(k+1)) :
    IsStationaryRate μ k S (S/(k+1)-∫ d, d ∂μ) := by sorry

end NahmiasPerishable.Inventory
