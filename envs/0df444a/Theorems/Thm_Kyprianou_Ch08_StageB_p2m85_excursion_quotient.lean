-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_excursion_quotient
-- name    : Kyprianou.Ch08.StageB.p2m85_excursion_quotient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:58:22.097638+00:00
-- url     : https://prove2.me/theorems/74a295a8-36e7-4fbc-9f7e-8458a8729369
-- title:
--   Excursion representation gives the oriented scale quotient
-- statement:
--   Excursion representation gives the oriented scale quotient
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_excursion_quotient
    (ψ : ℝ → ℝ) (V : ℝ → ℝ) (n : Measure ℝ)
    (hr : HasQExcursionScaleRepresentation ψ 0 V n)
    (a x : ℝ) (hA : 0 < a) (hB : 0 < a-x) :
    Real.exp (-Phi ψ 0*x - ∫ t in (a-x)..a, (n (Ici t)).toReal) =
      V (a-x) / V a := by
  sorry
