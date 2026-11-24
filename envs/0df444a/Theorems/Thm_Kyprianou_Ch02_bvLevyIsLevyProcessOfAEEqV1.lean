-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyIsLevyProcessOfAEEqV1
-- name    : Kyprianou.Ch02.bvLevyIsLevyProcessOfAEEqV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:40:52.584357+00:00
-- url     : https://prove2.me/theorems/350b4487-cab0-4cf8-b8f5-8852322a25e2
-- title:
--   Lévy property transfers along almost-sure path equality
-- statement:
--   Let $Y$ be a real Lévy process and let $Z$ be another real process with $Z_0=0$ identically. If $Y_t=Z_t$ for every $t\ge 0$ almost surely, then $Z$ is also a Lévy process: independent and stationary increments and càdlàg regularity pass from $Y$ to $Z$ along the almost-sure path identity.
-- source:
--   Kyprianou Ch.2 Exercise 2.8 / standard Lévy process AE-repair and drift lemmas

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyIsLevyProcessOfAEEqV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y Z : ℝ≥0 → Ω → ℝ)
    (hY : ProbabilityTheory.IsLevyProcess Y P)
    (hZ0 : Z 0 = fun _ => 0)
    (hae : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = Z t ω) :
    ProbabilityTheory.IsLevyProcess Z P := by sorry
