-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_strict_power_representatives
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_canonical_strict_power_representatives
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T22:26:31.016655+00:00
-- url     : https://prove2.me/theorems/6d1a580b-621a-489c-a1ef-9ba27d0b596f
-- title:
--   Strict weighted representatives for canonical logarithmic ideal powers
-- statement:
--   For the exact FixedData and positive common rational row scale R, canonical logarithmic ideal powers admit representatives of column-weight at most n delta for one fixed 0 < delta < R and all sufficiently large n. This retains the core geometric obligation. The proposed independent route is weighted blowup ampleness, a strict polarization margin, and eventual restriction surjectivity; compatibility with this exact ideal remains to be established.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_canonical_strict_power_representatives
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ delta : Real, 0 < delta ∧ delta < (R : Real) ∧
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ P : MvPolynomial (Fin (d.m + 1)) Complex,
          ∃ Q : MvPolynomial (Fin (d.m + 1)) Complex,
            P - Q ∈ (logarithmicCentersIdeal
              (fun j : Fin d.K => fun i =>
                (j.val : Complex) *
                  MatrixArithmetic.rationalCenters
                    (finiteNumerators d) (finiteDenominators d) i)
              (fun _ => e 0) e) ^ n ∧
            ∀ a ∈ Q.support,
              ∑ i, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                  (a i : Real) ≤ (n : Real) * delta := by sorry
