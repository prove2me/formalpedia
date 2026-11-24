-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinationCadlagCompositionV1
-- name    : Kyprianou.Ch02.subordinationCadlagCompositionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:32:04.360803+00:00
-- url     : https://prove2.me/theorems/42391169-1336-4eb2-82ab-560a46805d07
-- title:
--   subordinationCadlagComposition
-- statement:
--   subordinationCadlagComposition
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinationCadlagCompositionV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω)) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t => X (τ t ω) ω) := by sorry
