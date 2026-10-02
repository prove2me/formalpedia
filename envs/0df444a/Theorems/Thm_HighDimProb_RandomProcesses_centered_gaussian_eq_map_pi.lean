-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_centered_gaussian_eq_map_pi
-- name    : HighDimProb.RandomProcesses.centered_gaussian_eq_map_pi
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T08:48:08.305444+00:00
-- url     : https://prove2.me/theorems/a7021e01-763f-4d82-ad34-4d2dd7b82641
-- title:
--   Linear representation of centered finite Gaussian measures
-- statement:
--   Every centered Gaussian probability measure μ on a finite real coordinate space is the image of the product standard Gaussian measure under a continuous linear map L. The coordinate index may be empty and the covariance matrix may be singular. This provides the linear-image representation needed to apply the smooth Slepian comparison to arbitrary centered Gaussian laws.
-- source:
--   Supporting linear representation for Gaussian comparison. Uses Gaussian law uniqueness by mean and covariance and the positive-semidefinite covariance square root in Mathlib Probability/Distributions/Gaussian/Multivariate.lean and CharFun.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474. https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/Distributions/Gaussian/Multivariate.lean

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.centered_gaussian_eq_map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] (ι → ℝ),
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by sorry
