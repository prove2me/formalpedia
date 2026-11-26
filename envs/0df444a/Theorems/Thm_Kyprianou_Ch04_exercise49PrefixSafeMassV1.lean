-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PrefixSafeMassV1
-- name    : Kyprianou.Ch04.exercise49PrefixSafeMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:01:57.150191+00:00
-- url     : https://prove2.me/theorems/5c421ede-153b-56bc-987f-e018df84be12
-- title:
--   Independent safe future after a favourable prefix gives positive survival mass
-- statement:
--   Independent safe future after a favourable prefix gives positive survival mass
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PrefixSafeMassV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s : NNReal) (b : ℝ)
    (hA : 0 < P {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω})
    (hB : 0 < P {ω | ∀ u : NNReal, -b ≤ X u ω}) :
    0 < P {ω | ∀ u : NNReal, 0 ≤ X u ω} := by
  sorry
