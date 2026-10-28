-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_rat_eq_real
-- name    : OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_rat_eq_real
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T14:32:45.983811+00:00
-- url     : https://prove2.me/theorems/c1cf2a10-db20-4226-af3a-d5c8627333e3
-- title:
--   Rational weighted components agree with their real coercions
-- statement:
--   For any rational weights, rational cutoff, and multivariate polynomial, its weighted homogeneous component agrees with the component defined using the real coercions of those weights and cutoff.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_rat_eq_real
    {d : Nat} (w : Fin d → Rat) (q : Rat)
    (p : MvPolynomial (Fin d) Complex) :
    MvPolynomial.weightedHomogeneousComponent
        (fun k => (w k : Real)) (q : Real) p =
      MvPolynomial.weightedHomogeneousComponent w q p := by sorry
