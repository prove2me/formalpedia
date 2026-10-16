-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_flattened_coeff_finsupp
-- name    : OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T06:32:13.968613+00:00
-- url     : https://prove2.me/theorems/9c27bae5-3e78-43fc-a6f8-9eb20939dc74
-- title:
--   Coefficient splitting for finitely supported exponents
-- statement:
--   For any finitely supported exponent on the flattened variables, its coefficient is the coefficient in coordinate zero of the coefficient-ring coefficient selected by the successor coordinates.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp
    {m : Nat} (F : MvPolynomial (Fin m) (Polynomial Complex))
    (e : Fin (m + 1) →₀ Nat) :
    (MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ) F).coeff e =
      ((F.coeff (InterpolationMatrix.exponentVector (fun i => e i.succ))).coeff (e 0)) := by sorry
