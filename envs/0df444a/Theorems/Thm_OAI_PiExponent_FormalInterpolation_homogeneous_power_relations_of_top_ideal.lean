-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_power_relations_of_top_ideal
-- name    : OAI.PiExponent.FormalInterpolation.homogeneous_power_relations_of_top_ideal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:07:16.517376+00:00
-- url     : https://prove2.me/theorems/9c4f1e4a-9eb1-44dd-b51b-146cec6d665c
-- title:
--   Extract homogeneous witnesses for the variable power relations
-- statement:
--   For each variable, the ideal membership of one positive power can be represented using homogeneous coefficient polynomials of exactly the degree needed to match that power. This removes the graded-component extraction from the lifting argument. The boundary case `d = 0` is vacuous; for `d > 0`, the positive variable weights and the exact degree of the top components constrain the coefficient degrees. A proof route is to express ideal membership as a finite polynomial combination, decompose each coefficient by weighted degree, and retain the component matching the degree of the variable power.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.homogeneous_power_relations_of_top_ideal
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D)
    (f : Fin k → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ i, (w i : Real) * (a i : Real) ≤ D)
    (htop : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range fun j : Fin k =>
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) D (f j))) :
    ∃ e : Fin d → Nat, ∀ i, 0 < e i ∧
      ∃ q : Fin k → MvPolynomial (Fin d) Complex,
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ (e i) =
          ∑ j : Fin k, q j *
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j) ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous
          (fun i => (w i : Real)) (q j) ((e i : Real) * (w i : Real) - D) := by sorry
