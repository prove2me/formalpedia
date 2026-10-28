-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_sections_finite_witness_20261023_17
-- name    : OAI.PiExponent.FormalInterpolation.bounded_sections_finite_witness_20261023_17
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:22:41.496295+00:00
-- url     : https://prove2.me/theorems/4f5501bf-331c-4b17-9392-798716350f41
-- title:
--   Pointwise bounded sections admit a finite witness
-- statement:
--   From pointwise nonvanishing away from the origin, extract finitely many bounded sections whose degree-D components have common zero locus contained in the origin. Noetherianity of the polynomial ring gives a finite generating subfamily while retaining each section’s ordinary-power and support bounds.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_sections_finite_witness_20261023_17
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s D : Nat)
    (hpoint : ∀ (x : Fin d → Complex), (∃ i : Fin d, x i ≠ 0) →
      ∃ p : MvPolynomial (Fin d) Complex,
        p ∈ I ^ s ∧
        (∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) p) ≠ 0) :
    ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
      (∀ j, g j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (g j).support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
      (∀ (x : Fin d → Complex),
        (∀ (j : Fin m), MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) (g j)) = 0) →
          ∀ (i : Fin d), x i = 0) := by sorry
