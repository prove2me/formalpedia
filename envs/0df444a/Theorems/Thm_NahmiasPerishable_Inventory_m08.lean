-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m08
-- name    : NahmiasPerishable.Inventory.m08
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:29:49.445707+00:00
-- url     : https://prove2.me/theorems/89a8ea5e-1324-49cf-9d21-961172869751
-- title:
--   Continuous-review optimal zero-stock ordering
-- statement:
--   Weiss proves that an optimal policy orders only when the stock level is zero.
--
--   Differences from the source:
--   - reading: a continuous-review optimal ordering policy → measurable nonanticipating positive integer orders at locally finite epochs, with FIFO service and lost sales; reason: single-unit Poisson demand, zero lead time, and fixed lifetime are the stated model; demand at an ordering epoch is served before the replenishment
--   - encoding: infinite-horizon expected net cost per unit time → limsup of finite-time expected purchases, setup, holding and disposal costs minus actual sales revenue; reason: empty initial stock fixes the regenerative origin; the comparator class is not restricted to zero-stock ordering
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(iv), Continuous-review optimal zero-stock ordering (unnumbered), p. 687 (PDF 8), DOI:10.1287/opre.30.4.680; review attribution: Weiss [1980].

import Definitions.Def_NahmiasPerishable_Inventory_Continuous

open MeasureTheory

namespace NahmiasPerishable.Inventory

theorem m08 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℝ → ℝ) (P : WeissParams) (hP : ValidWeiss P)
    (hN : RankBasedSDI.LoadBalancing.IsPoissonProcess μ (Real.toNNReal P.rate) N) :
    ∃ π : ContinuousPolicy Ω, AdmissibleContinuous N P.life π ∧
      (∀ ρ : ContinuousPolicy Ω, AdmissibleContinuous N P.life ρ →
        continuousAverage μ N P π ≤ continuousAverage μ N P ρ) ∧
      (∀ᵐ ω ∂μ, ∀ i (t : ℝ), π.time i ω = (t : EReal) →
        continuousStock N P.life π true ω t = 0) := by sorry

end NahmiasPerishable.Inventory
