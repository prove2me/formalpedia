-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedOpenHitStrictSublevelsV1
-- name    : Kyprianou.Ch03.delayedOpenHitStrictSublevelsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T11:02:15.751804+00:00
-- url     : https://prove2.me/theorems/9934eefb-cd1d-4c5b-8f4a-1a3e5959ebfb
-- title:
--   Measurable strict sublevels of delayed open hitting
-- statement:
--   Use the rational witness lemma outside a measurable null set and use completion to include the exceptional event.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed open hitting stopping time.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedOpenHitStrictSublevelsV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (a : NNReal) (B : Set ℝ) (hB : IsOpen B) (s : NNReal) :
    MeasurableSet[F s] {w | sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) < (s : WithTop NNReal)} := by
  sorry
