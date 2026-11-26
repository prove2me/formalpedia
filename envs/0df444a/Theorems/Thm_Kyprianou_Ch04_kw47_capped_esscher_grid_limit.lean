-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_capped_esscher_grid_limit
-- name    : Kyprianou.Ch04.kw47_capped_esscher_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:59:41.681001+00:00
-- url     : https://prove2.me/theorems/d9a9e23a-c708-5dc6-abb5-8357b3537eb7
-- title:
--   Capped uniform Esscher grids converge to the signed Kella–Whitt increment
-- statement:
--   The exact pathwise product-grid limit specialises to the capped uniform mesh between arbitrary deterministic times, and its limit is the signed increment of the Kella–Whitt process.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_product_grid_pathwise_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The capped uniform grids have the actual signed Kella--Whitt
increment as their pointwise limit, including zero-length intervals. -/

theorem Kyprianou.Ch04.kw47_capped_esscher_grid_limit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (a b : NNReal) (hab : a ≤ b) (w : Ω) :
    let U := runningSup L
    let Z : NNReal → Ω → Real := fun t w => Real.exp (-alpha * (U t w-L.X t w))
    let J : NNReal → Ω → Real := fun t w =>
      ∫ s in Icc (0:Real) (t:Real), Z s.toNNReal w ∂volume
    let M : NNReal → Ω → Real := fun t w =>
      L.ψ alpha * J t w + 1 - Z t w - alpha * U t w
    let E : NNReal → Ω → Real := fun t w =>
      Real.exp (alpha * L.X t w - L.ψ alpha * (t:Real))
    let H : NNReal → Ω → Real := fun t w =>
      Real.exp (-alpha * U t w + L.ψ alpha * (t:Real))
    let u : Nat → Nat → NNReal := fun n i =>
      a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
    Tendsto (fun n => ∑ i ∈ Finset.range (n+1),
      H (u n i) w * (E (u n (i+1)) w - E (u n i) w)) atTop
      (nhds (M a w - M b w)) := by sorry
