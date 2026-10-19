-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesJet_monomial_coeff_eq_entry
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_coeff_eq_entry
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T13:06:32.057991+00:00
-- url     : https://prove2.me/theorems/b2f79d6f-9208-4fa2-8420-6252b40181c1
-- title:
--   Raw monomial coefficient identity for the formal series jet
-- statement:
--   For arbitrary exponents, the coefficient of the monomial with distinguished exponent h and remaining exponents a after applying the formal series jet, selected at distinguished degree s and remaining degrees b, equals the corresponding interpolation-matrix entry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_coeff_eq_entry
    {m : ℕ} (j s : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a b : Fin m → ℕ) :
  MvPowerSeries.coeff (InterpolationMatrix.exponentVector (Fin.cases s b))
      (seriesJet (fun i => (j : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)) =
    InterpolationMatrix.entry r G j s b h a := by sorry
