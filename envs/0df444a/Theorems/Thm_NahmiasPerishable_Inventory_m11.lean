-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m11
-- name    : NahmiasPerishable.Inventory.m11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:28:08.328978+00:00
-- url     : https://prove2.me/theorems/b1e27a2c-602c-4f71-bf43-f4d828fdb2b0
-- title:
--   Cohen two-period stationary distribution
-- statement:
--   In that case, the stationary distribution, say G(y), is given by
--   G(y) = F(y)·[1 − F(S − y)]/[1 − F(y)F(S − y)], for y ≥ 0
--   where F is the cumulative distribution of one period's demand.
--
--   Differences from the source:
--   - encoding: the stationary CDF fraction for all y ≥ 0 → the invariant law of A_next = max(D,S−A), together with nonzero denominator and the printed equality; reason: the denominator is a conclusion of the claimed formula, not a new assumption; the bounded-support counterexample I3 is retained
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(ii), Cohen two-period stationary distribution (unnumbered), p. 689 (PDF 10), DOI:10.1287/opre.30.4.680; review attribution: Cohen [1976]; Van Zyl [1964] for the analogous lost-sales result.

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory Set

namespace NahmiasPerishable.Inventory

theorem m11 (D : Demand) (S : ℝ) (hS : 0 ≤ S) (ν : Measure ℝ)
    (hν : ShockInvariant D.law (fun a d => max d (S-a)) ν)
    (hnonneg : ν (Ici 0) = 1) :
    ∀ y : ℝ, 0 ≤ y →
      1-cdf D.law y*cdf D.law (S-y) ≠ 0 ∧
      cdf ν y = cdf D.law y*(1-cdf D.law (S-y))/(1-cdf D.law y*cdf D.law (S-y)) := by sorry

end NahmiasPerishable.Inventory
