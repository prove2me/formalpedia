-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m23
-- name    : NahmiasPerishable.Inventory.m23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:28:27.134124+00:00
-- url     : https://prove2.me/theorems/08077bcf-2af0-4478-a226-f358c35e4e01
-- title:
--   Zero-lead-time decay admits myopic critical-number policies
-- statement:
--   s(y, t) = γ(y − t)⁺,
--   which will satisfy the requirements imposed by Veinott [1965] for the optimality of myopic policies. Hence it follows that a simple critical
--   number policy will be optimal.
--
--   Differences from the source:
--   - reading: the prose calls γ the fraction lost, but the display is s(y,t)=γ(y−t)⁺ → γ is the surviving fraction, while backlogged obligations do not decay; reason: the displayed transfer determines the convention
--   - encoding: expected costs and minimization → EReal infima, signed extended expectations, and an explicit definedness predicate; reason: undefined infinity minus infinity and nonmeasurable expectations are excluded; finite costs agree with ordinary expectations, while attainment is asserted in the conclusion
--   - encoding: myopic critical-number optimality → an optimizer of the one-step salvage-adjusted cost, optimal for every finite horizon and against every measurable demand-history rule for infinite discounted cost; reason: both lost sales and backorders are included, with zero setup cost and zero delivery lag
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §2.2.b, Zero-lead-time decay admits myopic critical-number policies (unnumbered), p. 699 (PDF 20), DOI:10.1287/opre.30.4.680; review attribution: Van Zyl [1964]; Veinott [1965] (also §1.2.b(iv), p. 691).

import Definitions.Def_NahmiasPerishable_Inventory_Decay

open MeasureTheory Set

namespace NahmiasPerishable.Inventory

theorem m23 (D : Demand) (b : Bool) (c h p alpha gamma : ℝ)
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (halpha : 0 < alpha ∧ alpha < 1) (hgamma : 0 < gamma ∧ gamma < 1)
    (hdefined : (decayControl D b c h p alpha gamma).defined {x | b = false → 0 ≤ x}) :
    ∃ S : ℝ, (b = false → 0 ≤ S) ∧
      (∀ z, (b = false → 0 ≤ z) →
        decayMyopic D b c h p alpha gamma S ≤ decayMyopic D b c h p alpha gamma z) ∧
      (∀ n x, (b = false → 0 ≤ x) →
        (decayControl D b c h p alpha gamma).optimal n x (pos (S-x))) ∧
      (∀ x, (b = false → 0 ≤ x) → ∃ π : HistoryPolicy,
        (∀ t d, π.rule t (hist d t) = pos (S-controlledStock b gamma x π d t)) ∧
        ∀ ρ : HistoryPolicy, decayPolicyCost D b c h p alpha gamma x π ≤
          decayPolicyCost D b c h p alpha gamma x ρ) := by sorry

end NahmiasPerishable.Inventory
