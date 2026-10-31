-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m07
-- name    : NahmiasPerishable.Inventory.m07
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:26.883485+00:00
-- url     : https://prove2.me/theorems/2fbe110b-ec6a-4224-b303-8f2c8b8f4920
-- title:
--   Equivalence of the two cost-accounting models
-- statement:
--   When n ≥ m, the optimal policies are structurally the same and are, in fact, identically the same when the future cost of outdating is discounted to the present in Nahmias' model by replacing θ with αᵐ⁻¹θ.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - encoding: expected costs and minimization → EReal infima, signed extended expectations, and an explicit definedness predicate; reason: undefined infinity minus infinity and nonmeasurable expectations are excluded; finite costs agree with ordinary expectations, while attainment is asserted in the conclusion
--   - encoding: identical optimal policies after discounting future outdating → equality of the two optimal-order correspondences with coefficient α^k θ; reason: arbitrary tie choices cannot create a spurious discrepancy; no equality is asserted in the final m−1 periods
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(ii), Equivalence of the two cost-accounting models (unnumbered), p. 686 (PDF 7), DOI:10.1287/opre.30.4.680; review attribution: Nahmias [1977a]; Fries [1975]; Nahmias [1975a].

import Definitions.Def_NahmiasPerishable_Inventory_Threshold

namespace NahmiasPerishable.Inventory

theorem m07 (k n : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) (D : Demand) (b : Bool)
    (t : Terminal) (c theta alpha : ℝ) (R : ℝ → EReal)
    (hc : 0 ≤ c) (htheta : 0 ≤ theta) (halpha : 0 < alpha ∧ alpha < 1)
    (hR : ∀ z, 0 ≤ R z)
    (hconv : ∀ u v a : ℝ, 0 ≤ a → a ≤ 1 →
      R (a*u+(1-a)*v) ≤ (a : EReal)*R u + ((1-a : ℝ) : EReal)*R v)
    (hF : (FixedLife.control (⟨D,b,.fries,t,c,theta,alpha,R⟩ : FixedLife k)).defined
      {x | canonical b x})
    (hN : (FixedLife.control (⟨D,b,.nahmias,t,c,alpha^k*theta,alpha,R⟩ : FixedLife k)).defined
      {x | canonical b x}) :
    ∀ x, canonical b x →
      {y | (FixedLife.control (⟨D,b,.fries,t,c,theta,alpha,R⟩ : FixedLife k)).optimal n x y} =
      {y | (FixedLife.control (⟨D,b,.nahmias,t,c,alpha^k*theta,alpha,R⟩ : FixedLife k)).optimal n x y} := by sorry

end NahmiasPerishable.Inventory
