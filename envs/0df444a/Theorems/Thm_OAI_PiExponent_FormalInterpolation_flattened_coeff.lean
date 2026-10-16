-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_flattened_coeff
-- name    : OAI.PiExponent.FormalInterpolation.flattened_coeff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T06:28:25.866865+00:00
-- url     : https://prove2.me/theorems/ccf64762-98c8-403c-9ed8-965109f4936f
-- title:
--   Coefficient extraction after polynomial flattening
-- statement:
--   Replacing the polynomial coefficient variable by coordinate zero and the other variables by successor coordinates identifies a full coefficient with the iterated coefficient.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.flattened_coeff
    {m : Nat} (F : MvPolynomial (Fin m) (Polynomial Complex))
    (a : Fin (m + 1) → Nat) :
    (MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ) F).coeff
        (InterpolationMatrix.exponentVector a) =
      ((F.coeff (InterpolationMatrix.exponentVector (fun i => a i.succ))).coeff (a 0)) := by sorry
