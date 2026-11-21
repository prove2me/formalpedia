-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
-- name    : Kyprianou.Ch08.StageB.source_result81_law_positive_mgf
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T13:59:03.538201+00:00
-- url     : https://prove2.me/theorems/99139220-c85a-4a27-bbce-f437a4e7240e
-- title:
--   Nonnegative real moments and the law-consistent triplet exponent
-- statement:
--   Use compensated truncated compound-Poisson laws and the matching Gaussian variance. Their positive exponential moments converge by the dominated compensated integrand and uniform integrability. Characteristic convergence identifies the limiting marginal. The characteristic exponent has positive triplet drift in the e^{iξX} convention, which is the negative of the first argument of tripletLaplace.
-- source:
--   Kyprianou (2006), Chapters 3 and 8, exponential moments and the Laplace characterization. Decomposition of 4aec3a48-841c-4d25-a6e1-3aeee066bb70.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_law_positive_mgf
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (t : ℝ≥0) (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun ω => Real.exp (β * D.X t ω)) P ∧
      (∫ ω, Real.exp (β * D.X t ω) ∂P) =
        Real.exp ((t : ℝ) *
          tripletLaplace (-D.triplet.drift) D.gaussianCoefficient D.triplet.levyMeasure β) := by
  sorry
