-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m22
-- name    : NahmiasPerishable.Inventory.m22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:58.469977+00:00
-- url     : https://prove2.me/theorems/4effdef9-abef-46a1-98ad-67a8f2159d4b
-- title:
--   Printed decay EOQ and pricing formulas
-- statement:
--   Then the optimal time between placement of orders as a function of price is given by Tₚ = √(2K/[λ(p)(cθ + h)]) and the profit rate, assuming one orders in an optimal manner, is given by
--   π(p) = pλ(p) − cλ(p) − √(2K[cθ + h]λ(p)).
--
--   Differences from the source:
--   - encoding: price-dependent demand λ(p) and exact optimal formulas → a fixed arbitrary price and its positive demand rate, using the exact exponential-decay cycle profit; reason: the same statement applies at every admissible price; the exact cycle cost is not replaced by a Taylor approximation despite I5
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §2.2.a, Printed decay EOQ and pricing formulas (unnumbered), p. 699 (PDF 20), DOI:10.1287/opre.30.4.680; review attribution: Cohen [1977].

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

namespace NahmiasPerishable.Inventory

theorem m22 (K c h theta price rate : ℝ) (hK : 0 < K) (hc : 0 ≤ c)
    (hh : 0 ≤ h) (htheta : 0 < theta) (hprice : 0 ≤ price) (hrate : 0 < rate)
    (hscale : 0 < c*theta+h) :
    let T := Real.sqrt (2*K/(rate*(c*theta+h)))
    0 < T ∧
    (∀ U, 0 < U → decayProfit K c h rate theta price U ≤ decayProfit K c h rate theta price T) ∧
    decayProfit K c h rate theta price T = price*rate-c*rate-Real.sqrt (2*K*(c*theta+h)*rate) := by sorry

end NahmiasPerishable.Inventory
