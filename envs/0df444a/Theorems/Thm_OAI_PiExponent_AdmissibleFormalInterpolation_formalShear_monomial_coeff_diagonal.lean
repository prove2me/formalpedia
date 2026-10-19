-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_diagonal
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:19:16.902097+00:00
-- url     : https://prove2.me/theorems/f8bcfa60-00ce-438c-bcb9-c1a41a821aac
-- title:
--   Diagonal coefficient of a sheared monomial
-- statement:
--   The coefficient at the original exponent of a monomial after applying the formal shear is one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (formalShear delta (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 1 := by sorry
