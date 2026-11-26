-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PrefixFutureMassV1
-- name    : Kyprianou.Ch04.exercise49PrefixFutureMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:59:35.103838+00:00
-- url     : https://prove2.me/theorems/c8d22ded-9444-4951-acef-9421a3a2cd7e
-- title:
--   Exact product mass of a favourable prefix and a measurable future path event
-- statement:
--   The deterministic-time restricted path law gives the product mass of the favourable prefix and any measurable future path event.
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PrefixFutureMassV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s : NNReal) (b : ℝ) (B : Set (NNReal → ℝ)) (hB : MeasurableSet B) :
    let A : Set Ω := {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω}
    P (A ∩ {ω | (fun u => X (s + u) ω - X s ω) ∈ B}) =
      P A * P {ω | (fun u => X u ω) ∈ B} := by
  sorry
