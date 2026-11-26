-- Prove2me | Theorems.Thm_Kyprianou_Ch04_unboundedBelowOfVanishingLaplace
-- name    : Kyprianou.Ch04.unboundedBelowOfVanishingLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:35:01.771813+00:00
-- url     : https://prove2.me/theorems/fbf9f48c-a929-5d53-b409-5b48fdd223a4
-- title:
--   Vanishing exponential expectations exclude finite lower bounds
-- statement:
--   A positive constant times the mass of each finite lower-bound event is bounded by an expectation tending to zero. Each event is null, and the union over integer lower bounds is exactly the bounded-below event.
-- source:
--   Kyprianou (2006), Chapter 4, Corollaries 4.9 and 4.12

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.unboundedBelowOfVanishingLaplace
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (g : ℕ → ℝ) (beta : ℝ)
    (hlim : Tendsto g atTop (nhds 0))
    (hbound : ∀ (K n : ℕ),
      Real.exp (-beta * (K : ℝ)) *
        (P {w | ∀ t : NNReal, -(K : ℝ) ≤ X t w}).toReal ≤ g n) :
    P {w | BddBelow (Set.range (fun t : NNReal => X t w))} = 0 := by
  sorry
