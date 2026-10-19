-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_top_sum_eq_coeff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_sum_eq_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:01:43.89398+00:00
-- url     : https://prove2.me/theorems/44a257a1-2367-4e4e-9a63-63c449519e57
-- title:
--   Top successor support sum isolates the target exponent
-- statement:
--   If every supported exponent attaining all the successor-coordinate bounds is e, then the finite sum over those exponents equals the single contribution indexed by e; this also covers the case that e is absent from the support, when both sides vanish.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_sum_eq_coeff
    {m : ℕ} (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (htop : ∀ a ∈ P.support, (∀ i : Fin m, a i.succ = e i.succ) → a = e) :
    (∑ a ∈ P.support.filter (fun a => ∀ i : Fin m, a i.succ = e i.succ),
      MvPolynomial.coeff a P *
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0))) =
      MvPolynomial.coeff e P *
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (e 0)) := by sorry
