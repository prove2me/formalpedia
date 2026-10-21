-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_total_degree_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_total_degree_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:59:16.460993+00:00
-- url     : https://prove2.me/theorems/95510fbb-5b94-47d4-a1b6-c19908d781ed
-- title:
--   Surjectivity of finite total-degree logarithmic jets
-- statement:
--   For any center and any prescribed complex coefficients on exponents of total degree at most N, there is a polynomial whose logarithmic jet has those coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_total_degree_surjective
    {m : Nat}
    (center : Fin m -> Complex)
    (N : Nat)
    (value : (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k, e k) <= N ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet center P) = value e := by sorry
