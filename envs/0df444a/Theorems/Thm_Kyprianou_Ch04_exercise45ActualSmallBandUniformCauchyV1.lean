-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ActualSmallBandUniformCauchyV1
-- name    : Kyprianou.Ch04.exercise45ActualSmallBandUniformCauchyV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:38:09.390929+00:00
-- url     : https://prove2.me/theorems/6a583c23-af76-51eb-922b-28b91beee4d9
-- title:
--   Actual small jump bands are uniformly Cauchy in cutoff on compact time windows
-- statement:
--   Apply countably many probability-zero tail events to obtain simultaneous uniform Cauchy estimates.
-- source:
--   Kyprianou (2006), Exercise 4.5 proof auxiliary

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45ActualSmallBandUniformCauchyV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hZero : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (univ : Set ℝ)) = 0) :
    let A : ℝ → NNReal → Ω → ℝ := fun e t w =>
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) - (t:ℝ)*∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
    ∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
      ∀ r q : ℝ, 0 < r → r < a → 0 < q → q < a →
        ∀ t ≤ T, |A r t w - A q t w| < δ := by sorry
