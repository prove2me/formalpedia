-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_subcritical_finite_adjoin
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_canonical_subcritical_finite_adjoin
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T22:56:52.228878+00:00
-- url     : https://prove2.me/theorems/f6485109-abc6-468e-a1bd-25bc1a63f8be
-- title:
--   Subcritical finite polynomial subalgebra inside a canonical logarithmic ideal power
-- statement:
--   Under exactly the parent's hypotheses, some positive power of the canonical logarithmic centers ideal contains finitely many polynomials of column-weight at most D<sR whose generated complex algebra makes the ambient polynomial ring a finite module. This finite geometric certificate retains the principal unresolved obligation.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_canonical_subcritical_finite_adjoin
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 ≤ D ∧ D < (s : Real) * (R : Real) ∧
        ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin (d.m + 1)) Complex,
          (∀ j, f j ∈ (logarithmicCentersIdeal
            (fun j : Fin d.K => fun i =>
              (j.val : Complex) *
                MatrixArithmetic.rationalCenters
                  (finiteNumerators d) (finiteDenominators d) i)
            (fun _ => e 0) e) ^ s) ∧
          (∀ j, ∀ a ∈ (f j).support,
            ∑ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (a i : Real) ≤ D) ∧
          Module.Finite (Algebra.adjoin Complex (Set.range f))
            (MvPolynomial (Fin (d.m + 1)) Complex) := by sorry
