-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaledProduct_family_bounds
-- name    : OAI.PiExponent.FormalInterpolation.scaledProduct_family_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T18:05:03.907932+00:00
-- url     : https://prove2.me/theorems/f0bda21e-c861-4532-a3a4-cc492ffcc32b
-- title:
--   Bounds for the indexed family of scaled products
-- statement:
--   For the family of all k-fold products, each product lies in I^(k*s), and every supported monomial has weight at most kD. Prove membership by multiplying the k memberships and using the ideal-power product law. Prove the support bound from the support-of-product inclusion and add the k given weight bounds. This remains valid for k=0 and for an empty support; in the target k is positive. No lower bound on individual weights is used.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.scaledProduct_family_bounds
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s : Nat) (hs : 0 < s) (D : Real)
    (k n N : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ D)
    (eFin : Fin N ≃ (Fin k → Fin n)) :
    (∀ j : Fin N, (∏ t : Fin k, f (eFin j t)) ∈ I ^ (k * s)) ∧
    (∀ j : Fin N, ∀ a ∈ (∏ t : Fin k, f (eFin j t)).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ (k : Real) * D) := by sorry
