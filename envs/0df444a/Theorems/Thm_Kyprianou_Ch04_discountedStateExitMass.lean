-- Prove2me | Theorems.Thm_Kyprianou_Ch04_discountedStateExitMass
-- name    : Kyprianou.Ch04.discountedStateExitMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:46:19.576744+00:00
-- url     : https://prove2.me/theorems/9f33bc4d-7dd9-46d8-ab88-8ae9fd36a84e
-- title:
--   discountedStateExitMass
-- statement:
--   Spatial exit bounds the discounted stopped absolute jump mass.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Spatial exit bounds the discounted stopped absolute jump mass. -/
theorem Kyprianou.Ch04.discountedStateExitMass {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (nu : Measure ℝ) (X L : NNReal → Ω → ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (l : ℝ) (hl : 0 ≤ l)
    (hi : ∀ y, Integrable (fun x => f (y+x)-f y) nu)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b nu ∧ ∀ z ∈ Icc (y-r) (y+r),
        ∀ᵐ x ∂nu, ‖f (z+x)-f z‖ ≤ b x)
    (hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (n : ℕ) (t : NNReal) :
    let tau : Ω → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
    let k := fun s x w => Real.exp (-l*s)*(f (L (Real.toNNReal s) w+x)-f (L s.toNNReal w))
    (∫⁻ w, ∫⁻ s in Icc (0:ℝ) (t:ℝ), ∫⁻ x,
      ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0|
      ∂nu ∂volume ∂P) < ⊤ := by
  sorry
