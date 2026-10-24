-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_initial_components_with_slack
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_initial_components_with_slack
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:08:44.463815+00:00
-- url     : https://prove2.me/theorems/0afd1fad-0fa1-410c-accc-af0322758a8e
-- title:
--   Curve bound gives bounded initial components with cutoff slack
-- statement:
--   Prove the geometric curve-bound-to-bounded-sections claim, with one unit of additional cutoff slack. The hypotheses and coordinate-component conclusion retain the parent’s finite-colength, positive-weight, nonnegative-slope, and positive-epsilon conditions. This isolates the geometric step from the parent’s natural-number cutoff rounding; the extra unit is available in principle by using part of the epsilon margin and choosing s sufficiently large. The research notes point to weighted compactification, ordinary blow-up, an ample perturbation, and eventual generation with ordinary Rees powers as a proof route. The substantial remaining core is to establish the common rational degree q and the coordinate relations from the uniform curve bound. In dimension zero the coordinate condition is empty, and the numerical witnesses exist since rho+eps>0.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_initial_components_with_slack
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧
            ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1)) := by sorry
