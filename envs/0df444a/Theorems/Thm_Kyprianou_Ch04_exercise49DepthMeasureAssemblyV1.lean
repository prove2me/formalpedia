-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DepthMeasureAssemblyV1
-- name    : Kyprianou.Ch04.exercise49DepthMeasureAssemblyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:45:34.396285+00:00
-- url     : https://prove2.me/theorems/1cc7738f-1c1d-5473-b937-ac3ded095f4e
-- title:
--   A stopped product law and depth splitting give the defective measure renewal equation
-- statement:
--   A stopped product law and depth splitting give the defective measure renewal equation
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DepthMeasureAssemblyV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set Ω) (hD : MeasurableSet D) (I V W : Ω → ℝ)
    (hI : Measurable I) (hV : Measurable V) (hW : Measurable W)
    (hZero : ∀ᵐ ω ∂P.restrict Dᶜ, V ω = 0)
    (hSplit : ∀ᵐ ω ∂P.restrict D, V ω = I ω + W ω)
    (hJoint : Measure.map (fun ω => (I ω, W ω)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map V P)) :
    Measure.map V P = P Dᶜ • Measure.dirac 0 +
      (Measure.map V P).conv (Measure.map I (P.restrict D)) := by
  sorry
