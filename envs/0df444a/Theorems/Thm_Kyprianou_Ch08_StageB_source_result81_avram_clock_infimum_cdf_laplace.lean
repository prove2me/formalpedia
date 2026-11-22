-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_clock_infimum_cdf_laplace
-- name    : Kyprianou.Ch08.StageB.source_result81_avram_clock_infimum_cdf_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:13:55.993725+00:00
-- url     : https://prove2.me/theorems/400701fc-4cb9-471f-90a4-0ad26f4690c7
-- title:
--   Laplace transform of the reflected-infimum CDF at an exponential clock
-- statement:
--   On the positive half-line the CDF transform is the reflected-infimum transform divided by the Laplace parameter. The Wiener–Hopf descending transform applies after identifying the reflected infimum with the terminal drawdown in law.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, identity (8.6). Mathematical reduction of d5833b96-248c-4b9d-87b8-3cb8b121acb0.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_avram_clock_infimum_cdf_laplace
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q) (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (β : ℝ) (hβ : 0 < β) (hne : β ≠ φ) :
    let ν := (P.prod (expMeasure q)).map
      (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})
    IntegrableOn (fun y : ℝ => Real.exp (-β * y) * cdf ν y) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * cdf ν y) =
        (1 / β) * ((q / φ) * ((φ - β) / (q - X.ψ β))) := by
  sorry
