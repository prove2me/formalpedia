-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_measure_scaling_zero
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:59:24.86093+00:00
-- url     : https://prove2.me/theorems/063c1297-01ac-4288-9890-1f2f16aea049
-- title:
--   Zero-radius simplex volume
-- statement:
--   At zero cutoff, the simplex is the origin when n is positive; when n is zero the domain is a singleton and 0^0 is 1. This establishes the boundary case required by the parent. A proof splits on n = 0: simplify the unique zero-dimensional function case, and for positive n show the cutoff set is the singleton zero function and use that a singleton has zero Lebesgue volume in positive dimension.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_zero
    (n : Nat) :
    MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ 0} =
      ENNReal.ofReal (0 ^ n) *
        MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
          ∑ i : Fin n, y i ≤ 1} := by sorry
