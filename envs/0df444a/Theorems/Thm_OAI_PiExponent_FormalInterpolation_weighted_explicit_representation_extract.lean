-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_explicit_representation_extract
-- name    : OAI.PiExponent.FormalInterpolation.weighted_explicit_representation_extract
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:12:36.569681+00:00
-- url     : https://prove2.me/theorems/e66a67e8-2f99-4a7e-ac01-cf1b5de5556e
-- title:
--   Extract homogeneous coefficients from an explicit representation
-- statement:
--   From an explicit representation of a degree-E homogeneous polynomial as a sum of coefficients times degree-D homogeneous generators, replace each coefficient by its degree-(E−D) weighted component and retain the representation. The proof route is to apply the degree-E component map to hrep, use that it is additive over the finite sum and that the degree-E component of a product with a degree-D homogeneous factor is the product of that factor with the coefficient’s degree-(E−D) component. The component-is-homogeneous theorem supplies the required coefficient degrees, while hf identifies the component of f with f. This preserves all degrees and works for zero polynomials and arbitrary real weights. The isolated core obligation is the component-product identity; once established, the extraction is finite-sum bookkeeping.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_explicit_representation_extract
    {d k : Nat} (w : Fin d → Rat)
    (D E : Real) (g : Fin k → MvPolynomial (Fin d) Complex)
    (f : MvPolynomial (Fin d) Complex)
    (a : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (hf : f.IsWeightedHomogeneous (fun i => (w i : Real)) E)
    (hrep : f = ∑ j : Fin k, a j * g j) :
    ∃ c : Fin k → MvPolynomial (Fin d) Complex,
      f = ∑ j : Fin k, c j * g j ∧
      ∀ j, (c j).IsWeightedHomogeneous (fun i => (w i : Real)) (E - D) := by sorry
