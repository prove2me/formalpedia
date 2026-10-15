-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_total_degree_series_jet_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.total_degree_series_jet_interpolation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:39:38.008767+00:00
-- url     : https://prove2.me/theorems/da0f615d-043a-4239-995f-7278620b6282
-- title:
--   Total-degree finite-series jet realization
-- statement:
--   For any center and total-degree cutoff, a polynomial realizes the coefficients of any formal power series at every exponent whose total degree is within the cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.total_degree_series_jet_interpolation
    {m : Nat}
    (center : Fin m -> Complex)
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by sorry
