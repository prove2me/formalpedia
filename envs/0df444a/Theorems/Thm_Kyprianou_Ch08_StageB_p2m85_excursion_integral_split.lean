-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_excursion_integral_split
-- name    : Kyprianou.Ch08.StageB.p2m85_excursion_integral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:58:20.119696+00:00
-- url     : https://prove2.me/theorems/5b596e3f-7522-44fa-82e7-75b3a7e70f3d
-- title:
--   Split the root and height contributions to the excursion integral
-- statement:
--   Split the root and height contributions to the excursion integral
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_excursion_integral_split
    (ψ : ℝ → ℝ) (V : ℝ → ℝ) (n : Measure ℝ)
    (hr : HasQExcursionScaleRepresentation ψ 0 V n)
    (u v : ℝ) (hu : 0 < u) (hv : u < v) :
    (∫ t in u..v, Phi ψ 0 + (n (Ici t)).toReal) =
      (v-u)*Phi ψ 0 + ∫ t in u..v, (n (Ici t)).toReal := by
  sorry
