-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_flattened_coeff_finsupp_monomial
-- name    : OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:36:33.417978+00:00
-- url     : https://prove2.me/theorems/e0636eab-7014-43ba-a06a-bcaf8f917925
-- title:
--   Coefficient splitting for a monomial
-- statement:
--   For a single multivariate monomial with polynomial coefficient, flattening preserves the coefficient obtained by selecting successor-coordinate exponents first and then the zeroth polynomial exponent.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp_monomial
    {m : Nat} (p : Polynomial Complex) (d : Fin m →₀ Nat)
    (e : Fin (m + 1) →₀ Nat) :
    (MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ)
      (MvPolynomial.monomial d p)).coeff e =
      ((MvPolynomial.monomial d p).coeff
        (InterpolationMatrix.exponentVector (fun i => e i.succ))).coeff (e 0) := by sorry
