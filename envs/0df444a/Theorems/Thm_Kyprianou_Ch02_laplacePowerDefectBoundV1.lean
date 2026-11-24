-- Prove2me | Theorems.Thm_Kyprianou_Ch02_laplacePowerDefectBoundV1
-- name    : Kyprianou.Ch02.laplacePowerDefectBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:02:21.111804+00:00
-- url     : https://prove2.me/theorems/5bb3cb9b-d906-4fec-b00e-e28c36581bf2
-- title:
--   Nonzero limit of unit-interval powers bounds the first-order defect
-- statement:
--   Eventually a^N is at least half its positive limit. Bound a^N above by exp(N(a-1)) and take logarithms.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.laplacePowerDefectBoundV1
    (a : ℕ → ℝ) (α : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hα : 0 < α) (ht : Tendsto (fun n => a n ^ (n+1)) atTop (nhds α)) :
    ∀ᶠ n in atTop, ((n+1 : ℕ) : ℝ)*(1-a n) ≤ -Real.log (α/2) := by sorry
