-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomialImage_substitution
-- name    : OAI.PiExponent.FormalInterpolation.monomialImage_substitution
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:58:24.405784+00:00
-- url     : https://prove2.me/theorems/c0c0c834-c9e0-4722-a3dc-1f49d160b3ed
-- title:
--   Monomial substitution agrees with the interpolation image
-- statement:
--   Evaluating the specified source monomial equals evaluating the variables of `monomialImage` at successor variables after mapping its polynomial coefficients into the zeroth variable.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.FormalInterpolation.monomialImage_substitution
    {m : Nat} (r : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (j h : Nat) (a : Fin m → Nat) :
    MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
        (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1))) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) (1 : Complex)) =
    MvPolynomial.aeval
      (fun i : Fin m => (MvPolynomial.X (i.succ : Fin (m + 1)) :
        MvPolynomial (Fin (m + 1)) Complex))
      (MvPolynomial.map
        (show Polynomial Complex →+* MvPolynomial (Fin (m + 1)) Complex from
          (Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) :
              MvPolynomial (Fin (m + 1)) Complex)).toRingHom)
        (InterpolationMatrix.monomialImage r G j h a)) := by sorry
