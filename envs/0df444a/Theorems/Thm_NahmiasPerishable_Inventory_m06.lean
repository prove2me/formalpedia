-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m06
-- name    : NahmiasPerishable.Inventory.m06
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:08.949316+00:00
-- url     : https://prove2.me/theorems/f9745647-74a7-4abc-94f7-385fd636c6c9
-- title:
--   General-lifetime future-outdating recursion
-- statement:
--   He shows that the expected outdating of the current order y (which will occur m periods from now) is given by ∫₀ʸ Gₘ(u, 𝐱)du where Gₘ is obtained by recursively solving
--   Gₙ[𝐱(n)] = ∫_0^{xₙ} Gₙ₋₁[v + xₙ₋₁, 𝐱(n − 2)]f(xₙ − v)dv
--   with G₁(x₁) = F(x₁) and 𝐱(n) = (xₙ, ⋯, x₁).
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - encoding: G recursion and expected current-order expiration → newest-first list recursion for G and an independent oldest-first FIFO path calculation; reason: the theorem identifies the two constructions; no future order can be served ahead of the current batch
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(ii), General-lifetime future-outdating recursion (unnumbered), p. 686 (PDF 7), DOI:10.1287/opre.30.4.680; review attribution: Nahmias [1975a]; Nahmias and Pierskalla [1975].

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory

namespace NahmiasPerishable.Inventory

theorem m06 (D : Demand) (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℝ) (y : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : 0 ≤ y) :
    (∫ d, batchExpiry (x,0) y d ∂demandPaths D.law (k+1)) =
      ∫ u in (0 : ℝ)..y, outdateCDF D (u :: (List.ofFn x).reverse) := by sorry

end NahmiasPerishable.Inventory
