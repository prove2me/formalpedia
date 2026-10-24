-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_witness_scale
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_power_witness_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:43:02.497787+00:00
-- url     : https://prove2.me/theorems/b163c13b-37fd-47a5-9550-c731870495c0
-- title:
--   Scale a coordinate power witness
-- statement:
--   Raising a positive coordinate power witness by a positive integer factor scales both its ideal exponent and its strict real weighted bound by that factor. Membership follows by multiplying the ideal-power membership through the corresponding power; positivity preserves the strict inequality.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinate_power_witness_scale {R : Type} [CommSemiring R] (I : Ideal R) (x : R) (w c : Real) (s n k : Nat) (hs : 0 < s) (hn : 0 < n) (hk : 0 < k) (hmem : x ^ n ∈ I ^ s) (hbound : (n : Real) * w < (s : Real) * c) : 0 < n * k ∧ x ^ (n * k) ∈ I ^ (s * k) ∧ (n * k : Real) * w < (s * k : Real) * c := by sorry
