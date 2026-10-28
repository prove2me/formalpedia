-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_component_relation_extracts_coordinate_power_20261024
-- name    : OAI.PiExponent.FormalInterpolation.component_relation_extracts_coordinate_power_20261024
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T15:20:37.569323+00:00
-- url     : https://prove2.me/theorems/13b0327a-0b87-4c73-a06c-1f8515cf6cff
-- title:
--   A coordinate relation in a component-closed ideal yields a coordinate power
-- statement:
--   From a nonzero relation among coordinate powers in a component-closed ideal, choose a nonzero coefficient at a positive index if one exists. The weighted component at that power’s degree isolates its scalar multiple, since the coordinate weight is positive and the powers have distinct degrees; cancel the nonzero scalar. If only the constant coefficient is nonzero, the relation puts a nonzero constant in the ideal, so `1 ∈ I` and `X i ∈ I`. This removes the degree-isolation and constant-case arguments from the parent. The coordinate and positivity hypotheses cover every actual coordinate; no coordinate exists when `d = 0`.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.component_relation_extracts_coordinate_power_20261024
    {d : Nat} (w : Fin d → Rat)
    (hw : ∀ j, 0 < (w j : Real))
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (hcomp : ∀ p ∈ I, ∀ r : Rat,
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) r p ∈ I)
    (i : Fin d)
    (hrel : ∃ (N : Nat) (c : Fin (N + 1) → Complex),
      (∃ k, c k ≠ 0) ∧
      (∑ k : Fin (N + 1),
        MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) ∈ I) :
    ∃ n : Nat, 0 < n ∧ MvPolynomial.X i ^ n ∈ I := by sorry
