-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_eq_zero_of_succ_lt
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_zero_of_succ_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:22:34.910592+00:00
-- url     : https://prove2.me/theorems/29998496-83c2-4982-8a8b-18024d55a69a
-- title:
--   Sheared monomial coefficients vanish above a successor exponent
-- statement:
--   If a target successor-coordinate exponent exceeds the corresponding exponent of the monomial, the sheared monomial has zero coefficient at that target exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_zero_of_succ_lt
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (hstrict : ∃ i : Fin m, a i.succ < e i.succ) :
    MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) = 0 := by sorry
