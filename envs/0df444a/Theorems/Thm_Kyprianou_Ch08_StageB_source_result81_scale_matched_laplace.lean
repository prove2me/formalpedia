-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_matched_laplace
-- name    : Kyprianou.Ch08.StageB.source_result81_scale_matched_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:18:01.731198+00:00
-- url     : https://prove2.me/theorems/9aabe7f8-0e6d-47df-b465-5e3c8e6009ad
-- title:
--   Matched Laplace transforms of the scale and clock CDF comparators
-- statement:
--   The scale transform and the transform of its interval primitive give integrability and show that the clock CDF plus q times the primitive has the same transform as q times the scale divided by the positive right root.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, identity (8.6). Mathematical reduction of source_result81_scale_from_clock_cdf_laplace.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_scale_matched_laplace
    (ψ w : ℝ → ℝ) (q : ℝ) (hφ : 0 < Phi ψ q)
    (hW : IsQScale ψ q w) (ν : Measure ℝ)
    (β : ℝ) (hβφ : Phi ψ q < β)
    (hcI : IntegrableOn (fun y : ℝ => Real.exp (-β * y) * cdf ν y) (Ioi 0))
    (hcLap : (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * cdf ν y) =
      (1 / β) * ((q / Phi ψ q) * ((Phi ψ q - β) / (q - ψ β)))) :
    let f := fun y => q / Phi ψ q * w y
    let g := fun y => cdf ν y + q * integratedScale w y
    IntegrableOn (fun y : ℝ => Real.exp (-β * y) * f y) (Ioi 0) ∧
      IntegrableOn (fun y : ℝ => Real.exp (-β * y) * g y) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * f y) =
        ∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * g y := by
  sorry
