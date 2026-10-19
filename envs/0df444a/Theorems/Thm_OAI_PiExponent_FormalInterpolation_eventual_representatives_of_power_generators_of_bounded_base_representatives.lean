-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_representatives_of_power_generators_of_bounded_base_representatives
-- name    : OAI.PiExponent.FormalInterpolation.eventual_representatives_of_power_generators_of_bounded_base_representatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:02:44.390472+00:00
-- url     : https://prove2.me/theorems/8f20e0f0-5d76-4cb6-8726-69329799a5e6
-- title:
--   Iterated reduction from bounded representatives and subcritical generators
-- statement:
--   Suppose every polynomial has a uniformly bounded weighted-degree representative modulo the positive power \(I^s\), and \(I^s\) has finitely many generators of weighted degree at most \(D<sR\). Then for every sufficiently large \(n\), every polynomial has a representative of weighted degree at most \(nR\) modulo \(I^n\).

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.eventual_representatives_of_power_generators_of_bounded_base_representatives
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (R : Real) (hR : 0 < R)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : D < (s : Real) * R)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (hspan : Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) = I ^ s)
    (hdeg : ∀ P ∈ S, ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ D)
    (C : Real)
    (hbase : ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : WeightedPolynomial w0 w C, P - Q.val ∈ I ^ s) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ P : MvPolynomial (Fin (m + 1)) Complex,
        ∃ Q : WeightedPolynomial w0 w ((n : Real) * R),
          P - Q.val ∈ I ^ n := by sorry
