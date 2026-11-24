-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatedIncrementCharMixtureV1
-- name    : Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:03:53.550825+00:00
-- url     : https://prove2.me/theorems/9939fe35-5280-4fdf-9883-9af4af30ad63
-- title:
--   subordinatedIncrementCharMixtureV1
-- statement:
--   subordinatedIncrementCharMixtureV1
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (s t : ℝ≥0) (hst : s ≤ t) (ξ : ℝ) :
    AEMeasurable (increment (fun t ω => X (τ t ω) ω) s t) P ∧
    charFun (P.map (increment (fun t ω => X (τ t ω) ω) s t)) ξ =
      ∫ ω, charFun (P.map (X (τ t ω - τ s ω))) ξ ∂P := by sorry
