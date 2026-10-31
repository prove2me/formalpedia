-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m04
-- name    : NahmiasPerishable.Inventory.m04
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:20.440626+00:00
-- url     : https://prove2.me/theorems/7ff04318-426e-470a-8494-6ed64c526025
-- title:
--   Two-period expected future outdating
-- statement:
--   Z = [y − (D₁ − x)⁺ − D₂]⁺,
--   from which one can show
--   E(Z) = ∫₀ʸ F(v + x)F(y − v)dv.
--
--   Differences from the source:
--   - encoding: two independent demand periods and their residual order → the product demand measure and FIFO batchExpiry; reason: the quantity is computed pathwise before integrating; bounded residual stock guarantees integrability
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(i), Two-period expected future outdating (unnumbered), p. 684 (PDF 5), DOI:10.1287/opre.30.4.680; review attribution: Nahmias and Pierskalla [1973].

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory

namespace NahmiasPerishable.Inventory

theorem m04 (D : Demand) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∀ d : Fin 2 → ℝ, (∀ i, 0 ≤ d i) →
      batchExpiry ((fun _ : Fin 1 => x),0) y d = pos (y-pos (d 0-x)-d 1)) ∧
    (∫ d, batchExpiry ((fun _ : Fin 1 => x),0) y d ∂demandPaths D.law 2) =
      ∫ v in (0 : ℝ)..y, cdf D.law (v+x)*cdf D.law (y-v) := by sorry

end NahmiasPerishable.Inventory
