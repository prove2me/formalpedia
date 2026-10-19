-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_representatives_of_subcritical_power_generators
-- name    : OAI.PiExponent.FormalInterpolation.eventual_representatives_of_subcritical_power_generators
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:55:27.971511+00:00
-- url     : https://prove2.me/theorems/b617b9f4-5588-4803-bda5-7f435e8262fd
-- title:
--   Eventual bounded representatives from subcritical ideal-power generators
-- statement:
--   A finite-colength polynomial ideal admits eventual representatives of weighted degree at most nR if some positive power has a finite generating family of weighted degree strictly below sR. Prove this independently by choosing finitely many representatives modulo I^s and iterating reduction by its generators. Modulo (I^s)^k, fewer than k generators occur in each product. Use k = ceil(n/s), replace a negative D by max(D,0), and absorb the fixed representative-degree constant using the strict inequality. This isolates the asymptotic algebra from all packet geometry.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.eventual_representatives_of_subcritical_power_generators
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I))
    (R : Real) (hR : 0 < R)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : D < (s : Real) * R)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (hspan : Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) = I ^ s)
    (hdeg : ∀ P ∈ S, ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ D) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ P : MvPolynomial (Fin (m + 1)) Complex,
        ∃ Q : WeightedPolynomial w0 w ((n : Real) * R),
          P - Q.val ∈ I ^ n := by sorry
