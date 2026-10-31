-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m05
-- name    : NahmiasPerishable.Inventory.m05
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:00.733153+00:00
-- url     : https://prove2.me/theorems/71b3b047-d5e2-4208-9008-0a719535df6a
-- title:
--   Two-period stationary ordering region and stock bounds
-- statement:
--   Mathematically, this is equivalent to assuming the initial condition C₀(x) = −cx.
--   That is, for each n ≥ 1, yₙ(x) > 0 if and only if x < x̄ where
--   x̄ = F⁻¹[(p − (1 − α)c)/(p + h)].
--   This particular form for x̄ assumes backordering. A similar result holds for lost sales.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - encoding: expected costs and minimization → EReal infima, signed extended expectations, and an explicit definedness predicate; reason: undefined infinity minus infinity and nonmeasurable expectations are excluded; finite costs agree with ordinary expectations, while attainment is asserted in the conclusion
--   - encoding: an optimal policy → existence of a family of actual Bellman minimizers; reason: ties are resolved by the existential selector, without assuming uniqueness or supplying the desired regularity as a hypothesis
--   - reading: inverse CDF and the analogous lost-sales critical number → lower generalized quantile in EReal for backorders, and the least minimizer of the associated nonperishable salvage-adjusted objective for lost sales; reason: no positive density or uniqueness is assumed; empty and unbounded quantile sets retain their infinite endpoints
--   - encoding: signed scalar starting stock → one physical-age coordinate plus a separate backlog, with C₀ = −c x; reason: negative stock denotes obligations, not goods that can expire; both strict stock bounds and the backlog equality are included
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(i), Two-period stationary ordering region and stock bounds (unnumbered), p. 684 (PDF 5), DOI:10.1287/opre.30.4.680; review attribution: Nahmias and Pierskalla [1973].

import Definitions.Def_NahmiasPerishable_Inventory_Threshold

open Set

namespace NahmiasPerishable.Inventory

theorem m05 (D : Demand) (b : Bool) (c h p theta alpha : ℝ)
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hp : 0 ≤ p) (htheta : 0 ≤ theta)
    (hscale : 0 < p+h) (halpha : 0 < alpha ∧ alpha < 1)
    (hdefined : (linearModel 1 D b .nahmias .salvage c h p theta alpha).control.defined
      {x | canonical b x}) :
    let M := linearModel 1 D b .nahmias .salvage c h p theta alpha
    let bar := critical D b c h p alpha
    ∃ q : ℕ → AgeState 1 → ℝ,
      (∀ n x, canonical b x → M.control.optimal n x (q n x)) ∧
      (∀ n x, canonical b x → (0 < q n x ↔ (total x : EReal) < bar)) ∧
      (∀ n x, canonical b x → 0 < total x → (total x : EReal) < bar →
        0 < total x+q n x ∧ ((total x+q n x : ℝ) : EReal) < bar) ∧
      (∀ n x, canonical b x → total x < 0 → q n x = |total x|+q n (0,0)) := by sorry

end NahmiasPerishable.Inventory
