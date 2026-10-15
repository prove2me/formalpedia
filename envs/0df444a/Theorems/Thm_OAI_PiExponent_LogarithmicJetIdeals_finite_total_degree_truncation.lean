-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_total_degree_truncation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_total_degree_truncation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:43:49.648682+00:00
-- url     : https://prove2.me/theorems/76144642-1bb0-427f-8b25-7408a3fc21cf
-- title:
--   Finite total-degree truncation of a formal series
-- statement:
--   Every multivariate formal power series has a total-degree truncation that vanishes in degrees strictly above N and preserves all coefficients of degree at most N. The strict cutoff retains the boundary degree N.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_total_degree_truncation
    {m : Nat}
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun T : MvPowerSeries (Fin (m + 1)) Complex =>
      ((e : Fin (m + 1) -> Nat) -> N < (∑ k : Fin (m + 1), e k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) T = 0) ∧
      ((e : Fin (m + 1) -> Nat) -> (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) T =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S) := by sorry
