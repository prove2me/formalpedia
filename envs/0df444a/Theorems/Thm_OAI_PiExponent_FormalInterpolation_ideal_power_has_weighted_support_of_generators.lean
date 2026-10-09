-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_power_has_weighted_support_of_generators
-- name    : OAI.PiExponent.FormalInterpolation.ideal_power_has_weighted_support_of_generators
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T18:33:01.472988+00:00
-- url     : https://prove2.me/theorems/c5aa216b-e0a1-49b1-ade2-ebf15e93e487
-- title:
--   Weighted support is preserved by powers of generated ideals
-- statement:
--   If a ring homomorphism sends every member of a finite generating family to a series supported in weighted degree at least R, then it sends every polynomial in the nth power of their generated ideal to a series supported in weighted degree at least nR.
-- source:
--   Weighted support under ideal multiplication, abstracting the ideal-power step in formalJet_mem_weighted_of_mem_pow from CompactJetPolynomial.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.ideal_power_has_weighted_support_of_generators
    {m : Nat} (v : Fin (m + 1) -> Real) (R : Real) (n : Nat)
    (f : RingHom (MvPolynomial (Fin (m + 1)) Complex) (MvPowerSeries (Fin (m + 1)) Complex))
    (x : Fin (m + 1) -> MvPolynomial (Fin (m + 1)) Complex)
    (hx : forall i, FormalInterpolation.hasWeightedSupport v R (f (x i)))
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : Membership.mem ((Ideal.span (Set.range x)) ^ n) P) :
    FormalInterpolation.hasWeightedSupport v ((n : Real) * R) (f P) := by sorry
