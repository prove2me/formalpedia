-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_coeff_eq_top_sum
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_eq_top_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:01:18.206774+00:00
-- url     : https://prove2.me/theorems/30de46fa-cd5e-48d4-a0ce-28680ffc25cc
-- title:
--   Shear coefficient reduces to top successor support
-- statement:
--   Under the coordinatewise successor-degree bounds, the sheared coefficient at e is a sum over only those supported exponents that attain every successor-coordinate bound. Each such term is the original polynomial coefficient multiplied by the zeroth-coordinate coefficient of the corresponding power of X.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_eq_top_sum
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hbound : ∀ a ∈ P.support, ∀ i : Fin m, a i.succ ≤ e i.succ) :
    MvPowerSeries.coeff e (formalShear delta P) =
      ∑ a ∈ P.support.filter (fun a => ∀ i : Fin m, a i.succ = e i.succ),
        MvPolynomial.coeff a P *
          PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0)) := by sorry
