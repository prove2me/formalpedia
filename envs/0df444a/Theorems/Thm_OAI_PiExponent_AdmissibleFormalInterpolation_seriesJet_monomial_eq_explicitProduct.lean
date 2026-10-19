-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesJet_monomial_eq_explicitProduct
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_eq_explicitProduct
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:35:02.999132+00:00
-- url     : https://prove2.me/theorems/9bef8025-e80d-4fcb-ad60-6519b8324893
-- title:
--   Monomial evaluation under the formal series jet
-- statement:
--   Evaluating the monomial under seriesJet gives the product of the substituted distinguished-variable image and the substituted images of the remaining variables, each raised to its exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_eq_explicitProduct
    {m : ℕ} (j : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a : Fin m → ℕ) :
  seriesJet (fun i => (j : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector (Fin.cases h a)) 1) =
    (1 + MvPowerSeries.X 0) ^ h *
      ∏ i, (MvPowerSeries.C ((j : ℂ) * r i) + MvPowerSeries.X i.succ +
        liftLogSeries m (G i : PowerSeries ℂ)) ^ a i := by sorry
