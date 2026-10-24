-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mapped_coeff_transport
-- name    : OAI.PiExponent.FormalInterpolation.mapped_coeff_transport
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:58:51.664605+00:00
-- url     : https://prove2.me/theorems/ff94d8ac-99ef-44c3-a8b6-3c7b561702dc
-- title:
--   Coefficient extraction through the polynomial embedding
-- statement:
--   After embedding polynomial coefficients into the zeroth variable and source variables into successor variables, the combined coefficient is the nested coefficient at degree `s` and exponent `b`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.FormalInterpolation.mapped_coeff_transport
    {m : Nat} (P : MvPolynomial (Fin m) (Polynomial Complex))
    (s : Nat) (b : Fin m → Nat) :
    (MvPolynomial.aeval
      (fun i : Fin m => (MvPolynomial.X (i.succ : Fin (m + 1)) :
        MvPolynomial (Fin (m + 1)) Complex))
      (MvPolynomial.map
        (show Polynomial Complex →+* MvPolynomial (Fin (m + 1)) Complex from
          (Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) :
              MvPolynomial (Fin (m + 1)) Complex)).toRingHom) P)).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((P.coeff (InterpolationMatrix.exponentVector b)).coeff s) := by sorry
