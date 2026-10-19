-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_subcritical_bounded_weight_span
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_subcritical_bounded_weight_span
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T12:40:35.580233+00:00
-- url     : https://prove2.me/theorems/504b84f3-4202-4440-950a-e5e0b2be0f5d
-- title:
--   Subcritical bounded-weight polynomials span a logarithmic center ideal power
-- statement:
--   For the actual fixed data and the exact truncation and scale hypotheses of the target, some positive power of the logarithmic center ideal is spanned by its members whose monomial supports have weighted degree at most a strict subcritical cutoff D < sR. This isolates the geometric spanning assertion; it does not itself extract a finite generating set.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_subcritical_bounded_weight_span
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Real, D < (s : Real) * (R : Real) ∧
      Ideal.span {P : MvPolynomial (Fin (d.m + 1)) Complex |
        P ∈ (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i =>
            (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ s ∧
        ∀ a ∈ P.support,
          ∑ i, InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ D} =
      (logarithmicCentersIdeal
        (fun j : Fin d.K => fun i =>
          (j.val : Complex) *
            MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
        T e) ^ s := by sorry
