-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_subcritical_logarithmic_power_generation
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_subcritical_logarithmic_power_generation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-18T07:55:43.108098+00:00
-- url     : https://prove2.me/theorems/a2004194-b4ef-40c4-81cd-523210aea598
-- title:
--   Subcritical finite generation of a logarithmic center ideal power
-- statement:
--   Under all original hypotheses, a positive power of the logarithmic center ideal has generators whose weighted degrees are strictly below sR. This is the main geometric obligation. Audit and port the source's uniform weighted curve inequality and blowup ampleness, retaining its positive sigma margin. Establish compatibility of arbitrary T and rational scales through weighted Newton filtrations, integral closures, and normalized blowups. Then use Serre vanishing, pushforward, and weighted section bounds to obtain finite ideal generators with strict degree slack. The equality case in the truncation bound must be handled by that filtration argument; literal equality of formal and truncated packets is unavailable. No geometric proof or compatibility certificate is claimed here.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_subcritical_logarithmic_power_generation
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
      ∃ S : Finset (MvPolynomial (Fin (d.m + 1)) Complex),
        Ideal.span (S : Set (MvPolynomial (Fin (d.m + 1)) Complex)) =
          (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i =>
            (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ s ∧
        ∀ P ∈ S, ∀ a ∈ P.support,
          ∑ i, InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ D := by sorry
