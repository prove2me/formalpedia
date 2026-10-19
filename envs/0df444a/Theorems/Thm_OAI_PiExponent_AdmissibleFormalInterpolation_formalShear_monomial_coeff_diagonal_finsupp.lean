-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_diagonal_finsupp
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal_finsupp
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T12:38:36.125232+00:00
-- url     : https://prove2.me/theorems/0f4caf85-c4e4-42a2-879b-76e5aa6e1d36
-- title:
--   Diagonal coefficient for a sheared monomial with finitely supported exponent
-- statement:
--   For any finitely supported exponent, shearing its monomial by adding arbitrary power series in the zeroth variable to the other variables preserves the coefficient at that same exponent as one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal_finsupp
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial e 1)) = 1 := by sorry
