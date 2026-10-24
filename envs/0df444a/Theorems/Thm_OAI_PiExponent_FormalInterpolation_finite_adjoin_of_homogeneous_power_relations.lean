-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_power_relations
-- name    : OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_power_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:07:33.47832+00:00
-- url     : https://prove2.me/theorems/1c3e69af-341c-4e5e-ae0e-f66f42890c71
-- title:
--   Lift finiteness from homogeneous power relations
-- statement:
--   A weighted-degree-bounded family whose degree-`D` components satisfy homogeneous power relations generates a finite extension algebra. This removes the main filtration-lifting argument from the parent. For `d = 0`, the polynomial ring is the base field; otherwise, clear denominators of the positive rational weights to use a natural-number degree and induct on it. The cutoff monomials with every exponent below the corresponding power are finite in number. For any other monomial, use a power relation: terms involving the original generators have coefficient degree smaller by `D > 0`, while replacing a top component by its lower-weight remainder strictly lowers degree. The remaining core obligation is formalizing this reduction and induction with Mathlib's support and weighted-component APIs.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_power_relations
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D)
    (f : Fin k → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ i, (w i : Real) * (a i : Real) ≤ D)
    (hrel : ∃ e : Fin d → Nat, ∀ i, 0 < e i ∧
      ∃ q : Fin k → MvPolynomial (Fin d) Complex,
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ (e i) =
          ∑ j : Fin k, q j *
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j) ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous
          (fun i => (w i : Real)) (q j) ((e i : Real) * (w i : Real) - D)) :
    Module.Finite (Algebra.adjoin Complex (Set.range f))
      (MvPolynomial (Fin d) Complex) := by sorry
