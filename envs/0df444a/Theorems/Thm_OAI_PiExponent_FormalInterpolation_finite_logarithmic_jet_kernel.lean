-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_logarithmic_jet_kernel
-- name    : OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_kernel
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T13:38:52.715012+00:00
-- url     : https://prove2.me/theorems/e2c50934-207d-44a9-90b3-70018ba3d121
-- title:
--   Nonzero polynomial in an underdetermined finite logarithmic jet system
-- statement:
--   For arbitrary centers and finite exponent sets S and T, if there are more allowed monomials than the K times |T| jet equations, a nonzero polynomial supported in S annihilates all those equations. Construct the linear map from monomial coefficients to jet coefficients, apply the finite-dimensional kernel criterion, and use monomial independence to preserve nonzeroness. No positivity or center separation is required.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_kernel
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (S T : Finset (Fin (m + 1) →₀ Nat))
    (hcard : K * T.card < S.card) :
    ∃ F : MvPolynomial (Fin (m + 1)) Complex,
      F ≠ 0 ∧ F.support ⊆ S ∧
        ∀ (j : Fin K) (a : Fin (m + 1) →₀ Nat), a ∈ T →
          MvPowerSeries.coeff a (formalJet (c j) F) = 0 := by sorry
