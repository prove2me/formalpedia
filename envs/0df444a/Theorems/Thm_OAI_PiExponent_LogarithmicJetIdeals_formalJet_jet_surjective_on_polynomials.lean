-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_jet_surjective_on_polynomials
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_jet_surjective_on_polynomials
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:49:15.330109+00:00
-- url     : https://prove2.me/theorems/0192e3b1-77ab-4f4f-b39c-8c60af002786
-- title:
--   Formal-jet substitution realizes every polynomial finite jet
-- statement:
--   For every center, cutoff N, and polynomial Q, some polynomial P has a formalJet whose coefficients agree with Q through total degree N.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_jet_surjective_on_polynomials
    {m : Nat}
    (center : Fin m -> Complex)
    (N : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q := by sorry
