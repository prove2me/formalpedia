-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalJet_finite_order_polynomial_pullback
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_finite_order_polynomial_pullback
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:39:46.133501+00:00
-- url     : https://prove2.me/theorems/d820ca80-13ce-4edc-aef9-9bd63f5f9f5f
-- title:
--   Polynomial pullback removing the formal logarithmic shift below a cutoff
-- statement:
--   For every natural cutoff T, one polynomial algebra endomorphism, independent of the center, turns formal-jet coefficients into ordinary Taylor coefficients at (1,c) whenever the first-coordinate exponent is strictly less than T.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_finite_order_polynomial_pullback
    {m : ℕ} (T : ℕ) :
    ∃ A : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
        MvPolynomial (Fin (m + 1)) ℂ,
      ∀ (c : Fin m → ℂ) (a : Fin (m + 1) →₀ ℕ),
        a 0 < T → ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
          MvPowerSeries.coeff a (formalJet c (A P)) =
            MvPowerSeries.coeff a
              ((MvPolynomial.aeval (fun i : Fin (m + 1) =>
                  MvPowerSeries.C
                    ((Fin.cases (1 : ℂ) c : Fin (m + 1) → ℂ) i) +
                  MvPowerSeries.X i) :
                MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
                  MvPowerSeries (Fin (m + 1)) ℂ) P) := by sorry
