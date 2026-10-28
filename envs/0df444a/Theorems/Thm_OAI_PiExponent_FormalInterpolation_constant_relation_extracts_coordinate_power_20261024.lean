-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_relation_extracts_coordinate_power_20261024
-- name    : OAI.PiExponent.FormalInterpolation.constant_relation_extracts_coordinate_power_20261024
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T15:27:33.203774+00:00
-- url     : https://prove2.me/theorems/7dcefae3-737e-4966-a795-60b4632365a2
-- title:
--   A nonzero constant relation yields a coordinate power
-- statement:
--   If every positive-index coefficient vanishes and the constant coefficient is nonzero, membership of the coordinate-power relation in I implies that I contains a nonzero constant. Since the coefficient ring is a field, I is the whole ring and X i ∈ I.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.constant_relation_extracts_coordinate_power_20261024
    {d : Nat} (i : Fin d) (I : Ideal (MvPolynomial (Fin d) Complex))
    (N : Nat) (c : Fin (N + 1) → Complex)
    (hc0 : c 0 ≠ 0)
    (hvanish : ∀ k : Fin (N + 1), k.val ≠ 0 → c k = 0)
    (hmem : (∑ k : Fin (N + 1),
      MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) ∈ I) :
    ∃ n : Nat, 0 < n ∧ MvPolynomial.X i ^ n ∈ I := by sorry
