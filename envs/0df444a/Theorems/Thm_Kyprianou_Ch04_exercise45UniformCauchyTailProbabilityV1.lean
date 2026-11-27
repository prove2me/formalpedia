-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45UniformCauchyTailProbabilityV1
-- name    : Kyprianou.Ch04.exercise45UniformCauchyTailProbabilityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:38:09.127529+00:00
-- url     : https://prove2.me/theorems/66ff26d7-cfc2-5b76-a933-eb998085e4c8
-- title:
--   Uniform two-parameter Poisson tail oscillation tends to zero in probability
-- statement:
--   Control the supremum over two cutoffs and all times in a compact horizon by a two-parameter maximal inequality.
-- source:
--   Kyprianou (2006), Exercise 4.5 proof auxiliary

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45UniformCauchyTailProbabilityV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hZero : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (univ : Set ℝ)) = 0) :
    let A : ℝ → NNReal → Ω → ℝ := fun e t w =>
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) - (t:ℝ)*∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
    ∀ (T : NNReal) (δ : ℝ), 0 < δ →
      Tendsto (fun n : ℕ => (P {w | ∃ r q : ℝ,
        0 < r ∧ r < 1/((n:ℝ)+1) ∧ 0 < q ∧ q < 1/((n:ℝ)+1) ∧
        ∃ t ≤ T, δ ≤ |A r t w-A q t w|}).toReal) atTop (nhds 0) := by sorry
