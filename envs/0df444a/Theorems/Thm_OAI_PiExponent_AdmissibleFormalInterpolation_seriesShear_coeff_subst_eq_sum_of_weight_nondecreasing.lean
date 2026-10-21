-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:20:40.6978+00:00
-- url     : https://prove2.me/theorems/3ff7d834-0ae7-4a09-a1dd-fca76914d5ac
-- title:
--   Finite coefficient formula for a weight-preserving formal shear
-- statement:
--   For a formal shear with zero constant terms whose monomial kernel cannot lower weight, each coefficient strictly below a positive weighted cutoff is computed by the finite shear matrix on the coefficients inside that cutoff. The input is an arbitrary multivariate power series.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i) (hH : 0 < H)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (htri : ∀ (a b : Fin (m + 1) → ℕ),
      (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
        (∑ i, Fin.cases v0 u i * (a i : ℝ)) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (seriesShear D
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0)
    (G : MvPowerSeries (Fin (m + 1)) ℂ)
    (b : ↥(strictWeightedSimplex (Fin.cases v0 u) H)) :
    (∑ a : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) G *
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (seriesShear D
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1))) =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) G) := by sorry
