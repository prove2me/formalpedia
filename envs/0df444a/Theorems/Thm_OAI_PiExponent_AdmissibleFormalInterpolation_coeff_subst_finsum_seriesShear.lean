-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_subst_finsum_seriesShear
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coeff_subst_finsum_seriesShear
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:16:35.991553+00:00
-- url     : https://prove2.me/theorems/5e44b236-965e-4e4d-aaa9-f8c38fa531aa
-- title:
--   Coefficient expansion of a formal shear substitution
-- statement:
--   For a zero-constant formal shear, the coefficient of a substituted arbitrary multivariate power series is the finsum of its monomial contributions. This removes the formal substitution expansion from the parent; prove it using the coefficient formula for MvPowerSeries substitution and identify the substituted monomial with its `seriesShear` image.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coeff_subst_finsum_seriesShear
    {m : ℕ} (D : Fin m → PowerSeries ℂ)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (G : MvPowerSeries (Fin (m + 1)) ℂ)
    (b : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) G) =
      ∑ᶠ a : Fin (m + 1) → ℕ,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) G *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
            (seriesShear D
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) := by sorry
