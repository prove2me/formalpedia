-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_diagonal_coeff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_diagonal_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:38:03.225986+00:00
-- url     : https://prove2.me/theorems/6f02c30a-1f68-4ec0-98c9-fce3ada38d00
-- title:
--   Diagonal coefficient of a sheared monomial
-- statement:
--   For the formal shear that fixes the zeroth variable and adds a series in that variable to each successor variable, the coefficient at exponent e of the image of the monomial with exponent e is one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_diagonal_coeff
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial e 1)) = 1 := by sorry
