-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:37:38.238576+00:00
-- url     : https://prove2.me/theorems/8e34a7e9-405c-4ec9-96d3-71a0e335f820
-- title:
--   Support constraints for a sheared monomial coefficient
-- statement:
--   A nonzero coefficient of the shear of a monomial has no larger exponent in any positive-index variable, and has a strictly smaller exponent in at least one such variable if the full exponent vectors differ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_support
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a b : Fin (m + 1) → ℕ)
    (hne : InterpolationMatrix.exponentVector a ≠ InterpolationMatrix.exponentVector b)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (formalShear delta (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1)) ≠ 0) :
    (∀ k : Fin m, (InterpolationMatrix.exponentVector a) k.succ ≤
      (InterpolationMatrix.exponentVector b) k.succ) ∧
    (∃ k : Fin m, (InterpolationMatrix.exponentVector a) k.succ <
      (InterpolationMatrix.exponentVector b) k.succ) := by sorry
