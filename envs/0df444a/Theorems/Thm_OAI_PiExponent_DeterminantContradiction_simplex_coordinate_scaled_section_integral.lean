-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_scaled_section_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_coordinate_scaled_section_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:45:07.968971+00:00
-- url     : https://prove2.me/theorems/b61de8a2-0a18-4117-8f7c-ac8c7459e363
-- title:
--   Scaled simplex sections under the integral
-- statement:
--   Integrating the volumes of the sections with cutoff 1−t gives the unit n-simplex volume times the integral of (1−t)^n, by scaling Lebesgue measure.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_coordinate_scaled_section_integral (n : Nat) :
    (∫ t in (0 : Real)..1, (MeasureTheory.volume {y : Fin n → Real |
      (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ 1 - t}).toReal) =
      (MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
        ∑ i : Fin n, y i ≤ 1}).toReal *
        (∫ t in (0 : Real)..1, (1 - t) ^ n) := by sorry
