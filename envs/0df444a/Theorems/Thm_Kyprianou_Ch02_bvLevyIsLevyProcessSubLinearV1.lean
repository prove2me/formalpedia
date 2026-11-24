-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyIsLevyProcessSubLinearV1
-- name    : Kyprianou.Ch02.bvLevyIsLevyProcessSubLinearV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:40:55.393634+00:00
-- url     : https://prove2.me/theorems/af62e438-3b55-43e7-9d66-680804f82e7c
-- title:
--   Subtracting a linear drift preserves the Lévy property
-- statement:
--   Let $Y$ be a real Lévy process on a probability space and let $c\in\mathbb{R}$ be deterministic. Then the drifted process
--   $$
--   Y^{(c)}_t := Y_t - c t
--   $$
--   is again a Lévy process: it starts at zero, has independent and stationary increments, and inherits càdlàg paths almost surely from $Y$.
-- source:
--   Kyprianou Ch.2 Exercise 2.8 / standard Lévy process AE-repair and drift lemmas

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyIsLevyProcessSubLinearV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ≥0 → Ω → ℝ) (hY : ProbabilityTheory.IsLevyProcess Y P) (c : ℝ) :
    ProbabilityTheory.IsLevyProcess (fun t ω => Y t ω - c * (t : ℝ)) P := by sorry
