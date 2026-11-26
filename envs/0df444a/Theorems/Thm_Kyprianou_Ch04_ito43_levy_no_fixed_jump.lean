-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_levy_no_fixed_jump
-- name    : Kyprianou.Ch04.ito43_levy_no_fixed_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:20:42.781175+00:00
-- url     : https://prove2.me/theorems/56a0945e-d4d5-4950-a232-8b4bf64f300b
-- title:
--   General Levy process has no jumps at deterministic positive times
-- statement:
--   At any fixed positive time a real Levy process equals its given almost sure left limit.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A real Levy process has no jump at any deterministic positive time. -/

theorem Kyprianou.Ch04.ito43_levy_no_fixed_jump {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (hLeft : ∀ᵐ w ∂P, Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Y t w))) :
    ∀ᵐ w ∂P, X t w = Y t w := by sorry
