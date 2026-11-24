-- Prove2me | Theorems.Thm_Kyprianou_Ch03_boundedCountableStoppedStateMeasurableV1
-- name    : Kyprianou.Ch03.boundedCountableStoppedStateMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:01:56.513927+00:00
-- url     : https://prove2.me/theorems/04c55e00-c074-4552-8c33-5600dfa23e64
-- title:
--   Bounded countable stopping time evaluation of an adapted state
-- statement:
--   Bounded countable stopping time evaluation of an adapted state
-- source:
--   Kyprianou (2006), Exercise 3.2

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.boundedCountableStoppedStateMeasurableV1
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (Z : NNReal → Omega → ℝ) (hAdapt : Adapted F Z)
    (g : Omega → NNReal)
    (hg : IsStoppingTime F (fun w => (g w : WithTop NNReal)))
    (hc : (Set.range (fun w => (g w : WithTop NNReal))).Countable)
    (s : NNReal) (hb : ∀ w, g w ≤ s) :
    Measurable[F s] (fun w => Z (g w) w) := by
  sorry
