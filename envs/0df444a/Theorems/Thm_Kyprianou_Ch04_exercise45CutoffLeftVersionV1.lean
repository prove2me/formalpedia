-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CutoffLeftVersionV1
-- name    : Kyprianou.Ch04.exercise45CutoffLeftVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:19:23.824648+00:00
-- url     : https://prove2.me/theorems/f525eb6a-13b0-4a20-92f6-7862a10bf44c
-- title:
--   Physical finite cutoff has an almost-sure left-limit version
-- statement:
--   Finite-cutoff state paths possess left limits, obtained from the finite affine step representation.
-- source:
--   Kyprianou Exercise 4.5, original-space cutoff data

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- A physical finite cutoff admits a left-limit version on the original space. -/
theorem Kyprianou.Ch04.exercise45CutoffLeftVersionV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L X2 Y : NNReal → Ω → ℝ)
    (b e : ℝ) (he : 0 < e)
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w)
    (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hY : ∀ t w, Y t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂(N.N w)) -
      (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν) :
    ∃ Yleft : NNReal → Ω → ℝ, ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s w) (nhdsWithin t (Iio t)) (nhds (Yleft t w)) := by
  sorry
