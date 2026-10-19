-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_power_generator_block_reduction
-- name    : OAI.PiExponent.FormalInterpolation.power_generator_block_reduction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:08:44.32276+00:00
-- url     : https://prove2.me/theorems/8e3c0b89-4a30-4c70-ae4c-c0913a6ae4ef
-- title:
--   Iterated bounded representatives across ideal-power blocks
-- statement:
--   Given bounded base representatives and generators of I^s whose weighted degrees are at most D, every polynomial has a representative modulo I^n of degree at most C + k * max(D, 0) whenever n ≤ (k + 1)s.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.power_generator_block_reduction
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (s : Nat) (hs : 0 < s)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (hspan : Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) = I ^ s)
    (D : Real)
    (hdeg : ∀ P ∈ S, ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ D)
    (C : Real)
    (hbase : ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : WeightedPolynomial w0 w C, P - Q.val ∈ I ^ s)
    (k n : Nat) (hn : n ≤ (k + 1) * s)
    (P : MvPolynomial (Fin (m + 1)) Complex) :
    ∃ Q : WeightedPolynomial w0 w (C + (k : Real) * max D 0),
      P - Q.val ∈ I ^ n := by sorry
