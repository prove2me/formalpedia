-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m21
-- name    : NahmiasPerishable.Inventory.m21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:48.700113+00:00
-- url     : https://prove2.me/theorems/47911961-3092-4631-99ab-64ecabbabf73
-- title:
--   Weibull-deterioration inventory balance
-- statement:
--   dI(t)/dt + αβtᵝ⁻¹I(t) = −λ,
--   where α and β are the shape parameters of the Weibull density.
--
--   Differences from the source:
--   - encoding: Weibull deterioration balance → inventory constructed from survival exp(−α t^β) and the survival-adjusted withdrawals; reason: the coefficient αβt^(β−1) is the hazard, not the density; positive times and the regular zero-time cases β ≥ 1 are included
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §2.2.a, Weibull-deterioration inventory balance (unnumbered), p. 699 (PDF 20), DOI:10.1287/opre.30.4.680; review attribution: Covert and Phillip [1973].

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

namespace NahmiasPerishable.Inventory

theorem m21 (a beta Q rate t : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hQ : 0 ≤ Q) (hrate : 0 ≤ rate) (ht : 0 < t ∨ (t = 0 ∧ 1 ≤ beta))
    (hphysical : ∀ u, 0 ≤ u → u ≤ t →
      0 ≤ survivalStock (fun s => Real.exp (-a*s^beta)) Q rate u) :
    HasDerivAt (survivalStock (fun s => Real.exp (-a*s^beta)) Q rate)
      (-rate-a*beta*t^(beta-1)*survivalStock (fun s => Real.exp (-a*s^beta)) Q rate t) t := by sorry

end NahmiasPerishable.Inventory
