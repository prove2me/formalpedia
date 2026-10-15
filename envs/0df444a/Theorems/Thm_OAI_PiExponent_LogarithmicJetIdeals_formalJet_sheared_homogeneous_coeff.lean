-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_sheared_homogeneous_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_homogeneous_coeff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:23:24.080776+00:00
-- url     : https://prove2.me/theorems/cba501aa-858e-4276-be20-da62c291dba4
-- title:
--   Sheared formal jets preserve homogeneous coefficients through their degree
-- statement:
--   For any homogeneous polynomial of degree n, the explicit centered and sheared substitution followed by formalJet preserves all coefficients of total degree at most n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_homogeneous_coeff
    {m : Nat}
    (center : Fin m -> Complex)
    (n : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex)
    (hhom : ∀ a : Finsupp (Fin (m + 1)) Nat,
      a ∈ Q.support -> (∑ k : Fin (m + 1), a k) = n)
    (e : Fin (m + 1) -> Nat)
    (he : (∑ k : Fin (m + 1), e k) <= n) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (formalJet center (MvPolynomial.aeval
        (Fin.cases (MvPolynomial.X 0 - MvPolynomial.C 1)
          (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) -
            (MvPolynomial.X 0 - MvPolynomial.C 1))) Q)) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) Q := by sorry
