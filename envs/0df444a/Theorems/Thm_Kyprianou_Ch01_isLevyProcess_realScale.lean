-- Prove2me | Theorems.Thm_Kyprianou_Ch01_isLevyProcess_realScale
-- name    : Kyprianou.Ch01.isLevyProcess_realScale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:25:20.592195+00:00
-- url     : https://prove2.me/theorems/7c17e39c-159b-4bc3-92c5-dc818ec7c077
-- title:
--   Constant real scaling preserves all four genuine Lévy-process properties
-- statement:
--   For every genuine real-valued Lévy process X and any real scaling constant c, the process cX also satisfies exactly the LeanLevy IsLevyProcess predicate: strict start-zero, finite-grid independent increments, stationary increments, and almost-sure cadlag sample paths. Independence and equality of laws transfer through the measurable scalar multiplication map, while cadlag regularity is preserved by continuous scalar multiplication. This is essential to scale a standard Brownian Lévy process by the square root of an arbitrary Gaussian variance in Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Pinned Mathlib iIndepFun.comp, IdentDistrib.comp, source-exact LeanLevy IsLevyProcess, Kyprianou (2006) Chapter 1 Theorem 1.6.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.isLevyProcess_realScale
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (c : ℝ)
    (h : IsLevyProcess X P) :
    IsLevyProcess (fun t ω => c * X t ω) P := by
  sorry
