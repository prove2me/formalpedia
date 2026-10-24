-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_logarithmic_component_normal_basis_bound
-- name    : OAI.PiExponent.FormalInterpolation.weighted_logarithmic_component_normal_basis_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T23:14:41.861614+00:00
-- url     : https://prove2.me/theorems/f73d3a80-61b7-4c60-b439-0c38a08aa19d
-- title:
--   Uniform weighted multiplicity bounds products of normal-basis weights
-- statement:
--   This specializes the manuscript's weighted transverse-multiplicity lemma to the logarithmic polynomial frame. Choose a common smooth point of the component outside Y=0, the other components, and the loci where the selected bases lose rank. For k = card A = card B, transverse B-flow coordinates and persistence give local length at least (epsilon N)^k/(k! product_B v), where epsilon = sigma/(m+2). Generic combinations of the equations and weighted Bézout give length at most N^k/product_A w. The weaker factor 2 k! epsilon^(-k) is bounded by the stated separation constant for 1 ≤ k ≤ m+1. This removes the uniform multiplicity comparison from the parent. No asymptotic threshold or coordinate-ratio hypothesis is assumed.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_logarithmic_component_normal_basis_bound
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (N : Nat) (hN : 0 < N)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hP : P ≠ ⊥) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ f ∈ S, logarithmicDegreeBound w (N : Real) f)
    (hwords : ∀ f ∈ S, ∀ word : List (Fin (m + 1)),
      logarithmicFrameCost v word <
        ((sigma : Real) / ((m : Real) + 2)) * (N : Real) →
      logarithmicFrameWord word f ∈ P) :
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      coordinateNormalBasisAtPrime P A →
      logarithmicNormalBasisAtPrime P B →
      (∏ i ∈ A, (w i : Real)) ≤
        interpolationSeparationConstant m sigma * (∏ i ∈ B, (v i : Real)) := by sorry
