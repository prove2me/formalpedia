-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_degree
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:19:39.965532+00:00
-- url     : https://prove2.me/theorems/2553bbc8-0009-425c-bec7-9e1d2bcf80ee
-- title:
--   Degree decreases in nonzero sheared monomial coefficients
-- statement:
--   For a nonzero coefficient in the shear of a monomial, distinct exponent vectors have strictly smaller total exponent in the variables indexed by `Fin m` via `Fin.succ`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_degree
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a b : Fin (m + 1) → ℕ)
    (hne : InterpolationMatrix.exponentVector a ≠ InterpolationMatrix.exponentVector b)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (formalShear delta (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1)) ≠ 0) :
    (∑ k : Fin m, (InterpolationMatrix.exponentVector a) k.succ) <
      (∑ k : Fin m, (InterpolationMatrix.exponentVector b) k.succ) := by sorry
