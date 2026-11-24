-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedNeighbourhoodClockBoundsV1
-- name    : Kyprianou.Ch03.delayedNeighbourhoodClockBoundsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:13:59.883516+00:00
-- url     : https://prove2.me/theorems/a6ea22d6-1a59-4a0f-9bc0-aa0363dffd88
-- title:
--   Delayed neighbourhood clocks increase below the closed hitting time
-- statement:
--   Nested open neighbourhoods give monotone infima; closed target witnesses belong to every neighbourhood; all witnesses are at least a.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed closed hitting approximation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedNeighbourhoodClockBoundsV1
    {Omega : Type} (X : NNReal → Omega → ℝ) (B : Set ℝ) (a : NNReal)
    (T : ℕ → Omega → WithTop NNReal)
    (hT : ∀ n w, T n w = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B})) (w : Omega) :
    Monotone (fun n => T n w) ∧
    (⨆ n, T n w) ≤ sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) ∧
    (a : WithTop NNReal) ≤ ⨆ n, T n w := by
  sorry
