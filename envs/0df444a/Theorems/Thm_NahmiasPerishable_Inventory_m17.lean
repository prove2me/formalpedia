-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m17
-- name    : NahmiasPerishable.Inventory.m17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:20.64297+00:00
-- url     : https://prove2.me/theorems/34949f78-8fe3-4a2f-ac5a-68830dcb6e4b
-- title:
--   Future outdating upper bound by the demand convolution
-- statement:
--   Expected outdating is estimated by the upper bound H(x + y) − H(x), where H(t) = ∫₀ᵗ Fᵐ*(u)du and Fᵐ* is the m-fold convolution of one period's demand.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - encoding: m-fold demand convolution and expected future expiration → CDF of the iid demand sum and the independently simulated FIFO batch residual; reason: the bounded order residual and bounded CDF integrals are integrable without a demand-moment assumption
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(iv), Future outdating upper bound by the demand convolution (unnumbered), p. 690 (PDF 11), DOI:10.1287/opre.30.4.680; review attribution: Nahmias [1976].

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory

namespace NahmiasPerishable.Inventory

theorem m17 (D : Demand) (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℝ) (y : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : 0 ≤ y) :
    (∫ d, batchExpiry (x,0) y d ∂demandPaths D.law (k+1)) ≤
      convolutionIntegral D.law (k+1) ((∑ i, x i)+y) -
        convolutionIntegral D.law (k+1) (∑ i, x i) := by sorry

end NahmiasPerishable.Inventory
