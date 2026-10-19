-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_eq_at_succ_eq
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_at_succ_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:23:03.678409+00:00
-- url     : https://prove2.me/theorems/1407f184-90aa-49e4-b748-a0e6f14ed421
-- title:
--   Sheared monomial coefficient at equal successor exponents
-- statement:
--   When all target successor-coordinate exponents equal the corresponding monomial exponents, the coefficient is the zeroth-coordinate coefficient of the corresponding power of $X$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_at_succ_eq
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, a i.succ = e i.succ) :
    MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) =
      PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0)) := by sorry
