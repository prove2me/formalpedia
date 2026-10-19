-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plainJet_shifted_monomial_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_coeff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T21:40:52.748985+00:00
-- url     : https://prove2.me/theorems/b0f0fc47-64a3-4947-aa37-fc1de658b7d2
-- title:
--   Coefficient of one shifted monomial under the plain jet
-- statement:
--   After applying plainJet to one scalar-weighted shifted monomial, the coefficient at exponent e is the scalar weight when the monomial exponent function is e, and zero otherwise.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_coeff
    {m : Nat} (c : Fin m -> Complex) (a : Complex)
    (d e : Fin (m + 1) -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.C a *
          Finset.prod Finset.univ (fun k : Fin (m + 1) =>
            (MvPolynomial.X k -
              MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) ^ d k))) =
      if d = e then a else 0 := by sorry
