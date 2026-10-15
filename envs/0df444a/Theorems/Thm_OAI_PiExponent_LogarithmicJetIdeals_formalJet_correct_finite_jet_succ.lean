-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_correct_finite_jet_succ
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_correct_finite_jet_succ
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:55:34.651668+00:00
-- url     : https://prove2.me/theorems/5db187de-21c6-47f0-9789-f5ea4bd5f369
-- title:
--   Correct one homogeneous degree of a formal jet
-- statement:
--   If a polynomial’s formal jet agrees with a target polynomial in every total degree strictly below n, then there is another polynomial whose formal jet still agrees below n and also agrees through degree n. The strict inequality makes the hypothesis vacuous at n = 0, and the degree-n correction preserves all lower-degree coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_correct_finite_jet_succ
    {m : Nat}
    (center : Fin m -> Complex)
    (n : Nat)
    (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (hbelow : (e : Fin (m + 1) -> Nat) ->
      (∑ k : Fin (m + 1), e k) < n ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (formalJet center P) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q) :
    Exists fun P' : MvPolynomial (Fin (m + 1)) Complex =>
      ((e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) < n ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P') =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q) ∧
      ((e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= n ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P') =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q) := by sorry
