-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaledProduct_component_identity
-- name    : OAI.PiExponent.FormalInterpolation.scaledProduct_component_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T18:14:46.998151+00:00
-- url     : https://prove2.me/theorems/696d4913-dce0-4172-abde-79103192960f
-- title:
--   Exact component of a product under a support bound
-- statement:
--   For polynomials whose supported monomials all have weighted degree at most D, the exact-kD component of a k-fold product is the product of the exact-D components of its factors. Each contributing tuple of supported monomials has total degree kD, so every factor must attain its bound.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.scaledProduct_component_identity
    {d : Nat} (w : Fin d → Rat) (D : Real) (k : Nat)
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ D)
    (N : Nat) (eFin : Fin N ≃ (Fin k → Fin n)) (j : Fin N) :
    MvPolynomial.weightedHomogeneousComponent
      (fun l => (w l : Real)) ((k : Real) * D)
      (∏ t : Fin k, f (eFin j t)) =
      ∏ t : Fin k, MvPolynomial.weightedHomogeneousComponent
        (fun l => (w l : Real)) D (f (eFin j t)) := by sorry
