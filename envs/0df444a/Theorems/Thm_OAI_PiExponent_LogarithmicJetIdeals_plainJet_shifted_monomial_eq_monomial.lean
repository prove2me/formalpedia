-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plainJet_shifted_monomial_eq_monomial
-- name    : OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_eq_monomial
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T21:49:16.954039+00:00
-- url     : https://prove2.me/theorems/c84e0863-c241-4e62-8a94-c33c81784a23
-- title:
--   Plain jet sends a shifted monomial to its formal monomial
-- statement:
--   Applying the plain jet to a scalar-weighted product of shifted variables raised to exponents d yields the formal-series monomial with exponent d and coefficient a. The claim includes zero exponents and the empty product.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_eq_monomial
    {m : Nat} (c : Fin m -> Complex) (a : Complex)
    (d : Fin (m + 1) -> Nat) :
    OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.C a *
          Finset.prod Finset.univ (fun k : Fin (m + 1) =>
            (MvPolynomial.X k -
              MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) ^ d k)) =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm d) a := by sorry
