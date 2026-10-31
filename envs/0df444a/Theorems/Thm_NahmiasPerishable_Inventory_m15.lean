-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m15
-- name    : NahmiasPerishable.Inventory.m15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:28:10.491194+00:00
-- url     : https://prove2.me/theorems/04424b3b-5f28-4a37-883c-91470fe59fa1
-- title:
--   Printed Chazan–Gal bounds and large-stock convergence
-- statement:
--   it leads to the general result that expected outdating per period is bounded below by μ₁(S) = S/m − D̄₁ and above by μ₂(S) = S/m − D̄₂ where D̄₁ is E(min(D, S/m)) and D̄₂ is E(min(D̄, S/m)) where D̄ is average demand over m days. These bounds are shown to converge to the true value of expected outdating as S grows large.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - encoding: average demand over m days and large-stock convergence → the iid product measure and two atTop limits of the printed bound errors; reason: all S ≥ 0 and every positive integer lifetime are included; no reversal of the printed bounds is made despite I2
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(ii), Printed Chazan–Gal bounds and large-stock convergence (unnumbered), p. 689 (PDF 10), DOI:10.1287/opre.30.4.680; review attribution: Chazan and Gal [1977].

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory Filter Topology

namespace NahmiasPerishable.Inventory

theorem m15 (μ : Measure ℝ) (hμ : DiscreteDemand μ) (k : ℕ) :
    ∃ rate : ℝ → ℝ,
      (∀ S, 0 ≤ S → IsStationaryRate μ k S (rate S) ∧
        lowerPrinted μ (k+1) S ≤ rate S ∧ rate S ≤ upperPrinted μ (k+1) S) ∧
      Tendsto (fun S => rate S-lowerPrinted μ (k+1) S) atTop (𝓝 0) ∧
      Tendsto (fun S => upperPrinted μ (k+1) S-rate S) atTop (𝓝 0) := by sorry

end NahmiasPerishable.Inventory
