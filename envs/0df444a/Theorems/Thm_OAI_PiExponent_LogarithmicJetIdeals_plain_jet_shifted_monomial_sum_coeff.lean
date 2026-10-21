-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_shifted_monomial_sum_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.plain_jet_shifted_monomial_sum_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:32:34.806411+00:00
-- url     : https://prove2.me/theorems/4f28fdc2-9f07-4940-9409-2c49a24277bd
-- title:
--   Coefficients of finite sums of shifted monomials
-- statement:
--   A finite sum of shifted monomials, weighted by a, has coefficient a e after applying plainJet when e belongs to the indexing set, and coefficient zero otherwise.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.plain_jet_shifted_monomial_sum_coeff
    {m : Nat} (c : Fin m -> Complex)
    (s : Finset (Fin (m + 1) -> Nat))
    (a : (Fin (m + 1) -> Nat) -> Complex)
    (e : Fin (m + 1) -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (Finset.sum s (fun d => MvPolynomial.C (a d) *
          Finset.prod Finset.univ (fun k : Fin (m + 1) => (MvPolynomial.X k -
            MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k))
              ^ d k)))) =
      if e ∈ s then a e else 0 := by sorry
