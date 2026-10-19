-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_ne_zero_imp_succ_le
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_ne_zero_imp_succ_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:28:05.687391+00:00
-- url     : https://prove2.me/theorems/a320e01a-db56-4c48-8068-81a5d0665559
-- title:
--   Nonzero sheared monomial coefficients respect successor exponents
-- statement:
--   If a coefficient of a sheared monomial is nonzero, each successor-coordinate exponent of its index is at most the corresponding exponent of the original monomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_ne_zero_imp_succ_le
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (hne : MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial a 1)) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ a i.succ := by sorry
