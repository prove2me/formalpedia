-- Prove2me | Theorems.Thm_OAI_PiExponent_AnalyticCollision_translated_cauchy_determinant_bound
-- name    : OAI.PiExponent.AnalyticCollision.translated_cauchy_determinant_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:36:00.390882+00:00
-- url     : https://prove2.me/theorems/cbe73501-147a-432a-933c-4004b72fbaea
-- title:
--   Multiplicative collision bound for translated Cauchy rows
-- statement:
--   A reusable analytic collision bound, independent of FixedData and weighted simplices. Normalize Taylor coefficients using the radius-R Cauchy estimate, expand the determinant, discard repeated degrees within each group, and bound the remaining geometric sum. Empty row sets give equality 1≤1; D=0 is also allowed. The strict condition s<1 ensures convergence.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.AnalyticCollision.translated_cauchy_determinant_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (F : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ)
    (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1) (hss : s * s = 1 / 2)
    (hF : ∀ a j, Differentiable ℂ (F a j))
    (hFD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖F a j z‖ ≤ D)
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun i j =>
      cauchyPowerSeries
        (fun t : ℂ => F (group i) j (center i + Complex.log (1 + t)))
        0 (1 / 2) (ell i) (fun _ => (1 : ℂ)))‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ i, ell i)) *
        s ^ (∑ a, (multiplicity group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by sorry
