-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PrefixBlockAppendV1
-- name    : Kyprianou.Ch04.exercise49PrefixBlockAppendV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:51.499262+00:00
-- url     : https://prove2.me/theorems/96060ec7-a579-547e-9a51-a645b2fda2d3
-- title:
--   Independent favourable prefixes concatenate with their gains added
-- statement:
--   Independent favourable prefixes concatenate with their gains added
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PrefixBlockAppendV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s t : NNReal) (b a : ℝ) (hb : 0 ≤ b)
    (hA : 0 < P {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω})
    (hB : 0 < P {ω | (∀ u : NNReal, u ≤ t → 0 ≤ X u ω) ∧ a ≤ X t ω}) :
    0 < P {ω | (∀ u : NNReal, u ≤ s + t → 0 ≤ X u ω) ∧ b + a ≤ X (s + t) ω} := by
  sorry
