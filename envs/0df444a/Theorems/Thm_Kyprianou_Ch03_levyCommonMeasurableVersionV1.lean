-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levyCommonMeasurableVersionV1
-- name    : Kyprianou.Ch03.levyCommonMeasurableVersionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:19:58.99745+00:00
-- url     : https://prove2.me/theorems/db43a966-a28b-4b59-9467-1a7820be6fca
-- title:
--   Lévy process admits a measurable-coordinate common path version
-- statement:
--   Choose a measurable whole-path version of the given process. It agrees outside a single null set; enforce zero initial value and càdlàg paths on the exceptional set and transfer the Lévy axioms.
-- source:
--   Kyprianou (2006), Exercise 3.1: right continuity of the completed natural filtration.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.levyCommonMeasurableVersionV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P) :
    ∃ Y : NNReal → Omega → ℝ, IsLevyProcess Y P ∧
      (∀ t, Measurable (Y t)) ∧ (∀ᵐ w ∂P, ∀ t, Y t w = X t w) := by
  sorry
