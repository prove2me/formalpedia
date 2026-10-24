-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_exact_rational_initial_components
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_exact_rational_initial_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:03:04.866223+00:00
-- url     : https://prove2.me/theorems/a66d55f8-c43d-4da4-8244-ab163f3c1b9d
-- title:
--   Curve bound gives coordinate relations at one rational weighted degree
-- statement:
--   Under the finite-colength and weighted curve-bound hypotheses, find a positive ordinary ideal power, a natural cutoff strictly below the epsilon-adjusted slope, and one positive rational weighted degree no larger than that cutoff such that every coordinate has a positive power in the span of that degree’s components from elements of the ideal power whose support weights are bounded by the degree. This is the geometric curve-bound-to-sections obligation; the proposed route is weighted blow-up positivity with the epsilon margin followed by eventual section generation. If `d = 0`, the coordinate condition is vacuous and the positive numerical witnesses exist because `rho + eps > 0`.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_exact_rational_initial_components
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) ≤ (B : Real) ∧
        ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
          MvPolynomial.X i ^ n ∈ Ideal.span (Set.range (fun (p :
            {g : MvPolynomial (Fin d) Complex //
              g ∈ I ^ s ∧
              ∀ a ∈ g.support,
                ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
            MvPolynomial.weightedHomogeneousComponent
              (fun j => (w j : ℚ)) q p.1)) := by sorry
