-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_eq_if_top
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_if_top
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:06:27.188688+00:00
-- url     : https://prove2.me/theorems/7b37d6ea-7a20-4a32-975c-59a1fab95cb8
-- title:
--   Monomial shear coefficient at bounded successor degrees
-- statement:
--   For a single monomial whose successor-coordinate exponents are bounded by the target, its sheared coefficient vanishes unless every bound is attained; when all are attained, the coefficient is the zeroth-coordinate coefficient of the corresponding power of `X`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_if_top
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (hbound : ∀ i : Fin m, a i.succ ≤ e i.succ) :
    MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) =
      if ∀ i : Fin m, a i.succ = e i.succ then
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0))
      else 0 := by sorry
