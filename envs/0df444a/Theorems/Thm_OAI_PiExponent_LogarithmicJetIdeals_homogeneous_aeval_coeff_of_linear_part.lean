-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_aeval_coeff_of_linear_part
-- name    : OAI.PiExponent.LogarithmicJetIdeals.homogeneous_aeval_coeff_of_linear_part
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:28:23.278995+00:00
-- url     : https://prove2.me/theorems/4e31257f-6e06-47e8-8874-3c2b1a1120a5
-- title:
--   Homogeneous polynomial coefficients under a substitution with fixed linear part
-- statement:
--   If every series substituted for a variable has the same constant and linear coefficients as that variable, then evaluating a homogeneous degree-`n` polynomial preserves every coefficient of total degree at most `n`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.homogeneous_aeval_coeff_of_linear_part
    {m : Nat}
    (R : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex)
    (n : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex)
    (hhom : ∀ a : Finsupp (Fin (m + 1)) Nat,
      a ∈ Q.support -> (∑ k : Fin (m + 1), a k) = n)
    (hR : ∀ (i : Fin (m + 1)) (d : Fin (m + 1) -> Nat),
      (∑ k : Fin (m + 1), d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : Fin (m + 1) -> Nat)
    (he : (∑ k : Fin (m + 1), e k) <= n) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval R Q) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) Q := by sorry
