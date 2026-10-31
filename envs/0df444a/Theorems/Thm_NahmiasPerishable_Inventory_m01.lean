-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m01
-- name    : NahmiasPerishable.Inventory.m01
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:31.883347+00:00
-- url     : https://prove2.me/theorems/d73a1ab4-c3ec-43f0-a4ad-a89bec37495c
-- title:
--   Fixed-life EOQ
-- statement:
--   The optimal batch size which minimizes the holding and set-up cost rate is Q* = √(2Kλ/h), where K is the set-up cost per order, λ the demand rate and h the cost of holding a unit for a unit time. Then it is easy to see that the optimal order size is a = min(Q*, λm) which ensures that no units expire.
--
--   Differences from the source:
--   - encoding: optimal EOQ subject to expiration → minimization of the actual cycle rate over every positive real batch size; reason: cycle length is min(Q/λ,m); expiration is allowed in the comparison class and excluded by the conclusion
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.1, Fixed-life EOQ (unnumbered), p. 682 (PDF 3), DOI:10.1287/opre.30.4.680; review attribution: Review example (standard EOQ).

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

namespace NahmiasPerishable.Inventory

theorem m01 (K h rate life : ℝ) (hK : 0 < K) (hh : 0 < h)
    (hrate : 0 < rate) (hlife : 0 < life) :
    let Q := min (Real.sqrt (2*K*rate/h)) (rate*life)
    0 < Q ∧ (∀ R, 0 < R → fixedCycleCost K h rate life Q ≤ fixedCycleCost K h rate life R) ∧
      pos (Q-rate*life) = 0 := by sorry

end NahmiasPerishable.Inventory
