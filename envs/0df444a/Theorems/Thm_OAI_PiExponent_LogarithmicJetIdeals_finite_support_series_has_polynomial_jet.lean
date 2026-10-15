-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_support_series_has_polynomial_jet
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_support_series_has_polynomial_jet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:48:50.035281+00:00
-- url     : https://prove2.me/theorems/b04e81d5-bfe6-4ece-8657-5f293e25f0ed
-- title:
--   Finite support admits a polynomial representative through a total-degree cutoff
-- statement:
--   If a series has zero coefficients above total degree N, its total-degree truncation at N + 1 is a polynomial with the same coefficients through degree N.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_support_series_has_polynomial_jet
    {m : Nat}
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex)
    (hS : (e : Fin (m + 1) -> Nat) -> N < (∑ k : Fin (m + 1), e k) ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S = 0) :
    Exists fun Q : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by sorry
