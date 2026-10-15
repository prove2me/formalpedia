-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomial_finite_coefficient_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.polynomial_finite_coefficient_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:27:04.231652+00:00
-- url     : https://prove2.me/theorems/85aac758-cf6b-484b-900b-abcb15707d36
-- title:
--   Polynomial encoding of finite coefficient data
-- statement:
--   Any values prescribed at a finite family of distinct multi-indices are the corresponding coefficients of some multivariate polynomial, regarded as a multivariate power series.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.polynomial_finite_coefficient_interpolation
    {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (degree : α → Fin (m + 1) → ℕ)
    (hdegree : Function.Injective degree) (value : α → ℂ) :
    ∃ R : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (MvPolynomial.toMvPowerSeries R) = value b := by sorry
