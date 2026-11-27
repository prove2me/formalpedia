-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalFiniteVariationGridEnvelopeV1
-- name    : Kyprianou.Ch04.physicalFiniteVariationGridEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:39:14.334887+00:00
-- url     : https://prove2.me/theorems/83e4f331-d6fc-5bf2-8f94-d3b0e877645b
-- title:
--   physicalFiniteVariationGridEnvelopeV1
-- statement:
--   Physical finite variation uniform grid envelope.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A common physical finite-variation state has uniform grid convergence
under compact convergence of the states defining its normalised weights. -/

theorem Kyprianou.Ch04.physicalFiniteVariationGridEnvelopeV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (T : NNReal) (b K : ℝ) (hK : 0 ≤ K)
    (X L V : NNReal → Ω → ℝ) (Y U : ℕ → NNReal → Ω → ℝ)
    (g : ℝ → ℝ → ℝ)
    (hLip : ∀ s : NNReal, ∀ x y : ℝ, |g s x-g s y| ≤ K * |x-y|)
    (hV : ∀ t w, V t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hAtoms : ∀ᵐ w ∂P, ∃ S : Finset NNReal,
      (∀ r ∈ S, 0 < r ∧ r ≤ T ∧ 1/2 < |X r w-L r w|) ∧
      (N.N w).restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
        ∑ r ∈ S, Measure.dirac ((r : ℝ),X r w-L r w))
    (hX : ∀ᵐ w ∂P, ∀ t, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hY : ∀ᵐ w ∂P, ∀ m t, 0 < t →
      Tendsto (fun s => Y m s w) (nhdsWithin t (Iio t)) (nhds (U m t w)))
    (D : ℕ → Ω → ℝ≥0∞) (hD : ∀ m, Measurable (D m))
    (hb : ∀ᵐ w ∂P, ∀ m t, t ≤ T → ENNReal.ofReal |Y m t w-X t w| ≤ D m w)
    (hc : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N,
      D m w ≤ ENNReal.ofReal d) :
    let G := fun (H : NNReal → Ω → ℝ) (n : ℕ) (t : NNReal) w =>
      ∑ k ∈ Finset.range n, H (T * (k : NNReal) / (n : NNReal)) w *
        (V (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
          V (min t (T * (k : NNReal) / (n : NNReal))) w)
    let H := fun (s : NNReal) w => if s = 0 then 0 else g (s : ℝ) (L s w)
    let Hc := fun m (s : NNReal) w => if s = 0 then 0 else g (s : ℝ) (U m s w)
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, (P {w | ∃ t ≤ T, δ ≤ |G (Hc m) n t w-G H n t w|}).toReal ≤ η := by
  sorry
