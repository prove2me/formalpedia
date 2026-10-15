-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_support_jet_realization
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_support_jet_realization
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:44:16.250335+00:00
-- url     : https://prove2.me/theorems/c7f62beb-45eb-493d-9fdb-f18635cb4d81
-- title:
--   Finite-support total-degree jet realization
-- statement:
--   If a multivariate formal power series has no nonzero coefficients above total degree N, then some polynomial has the same coefficients through degree N after applying formalJet at any chosen center. This isolates the finite-jet interpolation step.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_support_jet_realization
    {m : Nat}
    (center : Fin m -> Complex)
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex)
    (hS : (e : Fin (m + 1) -> Nat) -> N < (∑ k : Fin (m + 1), e k) ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S = 0) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by sorry
