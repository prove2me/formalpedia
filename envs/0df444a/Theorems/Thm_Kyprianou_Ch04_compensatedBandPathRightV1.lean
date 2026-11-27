-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compensatedBandPathRightV1
-- name    : Kyprianou.Ch04.compensatedBandPathRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:50:48.38307+00:00
-- url     : https://prove2.me/theorems/6b38a9b6-9aa1-5b17-a9b3-32b427989774
-- title:
--   compensatedBandPathRightV1
-- statement:
--   Finite-band compensated Poisson paths are almost surely right continuous.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.compensatedBandPathRightV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (N : PoissonRandomMeasure.{0,0,0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (Y : NNReal → Ω → ℝ)
    (hY : ∀ t w, Y t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N w)) -
      (t : ℝ) * (∫ x in B,x ∂ν)) :
    ∀ᵐ w ∂P, ∀ t, Tendsto (fun s => Y s w) (𝓝[>] t) (𝓝 (Y t w)) := by
  sorry
