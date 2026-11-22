-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_from_clock_cdf_laplace
-- name    : Kyprianou.Ch08.StageB.source_result81_scale_from_clock_cdf_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:14:01.534155+00:00
-- url     : https://prove2.me/theorems/be98aec9-15a5-4e3f-98d2-8ef7e13914e9
-- title:
--   Scale-function identity from the reflected-infimum CDF transform
-- statement:
--   For a nonnegative probability law with the stated descending CDF transform, Laplace uniqueness identifies its CDF plus the integrated scale function with the appropriately normalized scale function. At zero use right continuity. Negative reserves give zero CDF and zero scale terms.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, identity (8.6). Mathematical reduction of d5833b96-248c-4b9d-87b8-3cb8b121acb0.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_scale_from_clock_cdf_laplace
    (ψ w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (hφ : 0 < Phi ψ q)
    (hW : IsQScale ψ q w) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hs : ν (Iio (0 : ℝ)) = 0)
    (hc : ∀ β : ℝ, Phi ψ q < β →
      IntegrableOn (fun y : ℝ => Real.exp (-β * y) * cdf ν y) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * cdf ν y) =
        (1 / β) * ((q / Phi ψ q) * ((Phi ψ q - β) / (q - ψ β))))
    (x : ℝ) :
    1 - cdf ν x = Zscale q w x - q / Phi ψ q * w x := by
  sorry
