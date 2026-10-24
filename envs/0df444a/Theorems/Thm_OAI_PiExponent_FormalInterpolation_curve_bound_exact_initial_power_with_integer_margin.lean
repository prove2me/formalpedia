-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_exact_initial_power_with_integer_margin
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_exact_initial_power_with_integer_margin
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T19:01:00.172837+00:00
-- url     : https://prove2.me/theorems/73565471-a66a-4809-8539-7f893ed50c23
-- title:
--   Curve bound gives exact-degree coordinate relations with integer margin
-- statement:
--   Under the finite-colength and weighted curve-bound hypotheses, find a positive ideal power, a strict natural cutoff below the ε-adjusted slope, and one rational weighted degree q ≤ B such that every coordinate has a positive power in the span of degree-q components of elements of that ideal power whose support weights are at most q. The remaining core is deriving this common-degree generation statement from the curve bound, via the weighted blow-up and eventual section generation described in the source.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_exact_initial_power_with_integer_margin
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∃ q : Rat, (q : Real) ≤ (B : Real) ∧
        ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
          MvPolynomial.X i ^ n ∈ Ideal.span (Set.range (fun (p :
            {g : MvPolynomial (Fin d) Complex //
              g ∈ I ^ s ∧
              ∀ a ∈ g.support,
                ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
            MvPolynomial.weightedHomogeneousComponent
              (fun j => (w j : ℚ)) q p.1)) := by sorry
