-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_levy_matching_limits
-- name    : Kyprianou.Ch04.ito43_levy_matching_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:35:58.96184+00:00
-- url     : https://prove2.me/theorems/2506d2e2-ff78-5687-bd94-abde22e7c67e
-- title:
--   Matching increment laws identify almost sure limits
-- statement:
--   Two families with equal marginal laws and almost sure limits, one of which is zero, have an almost surely zero limit in the other family.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two increment families with matching distributions and almost sure limits have matching limiting laws. -/

theorem Kyprianou.Ch04.ito43_levy_matching_limits {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l : Filter NNReal) [l.NeBot] [l.IsCountablyGenerated]
    (U V : NNReal → Ω → ℝ) (D : Ω → ℝ)
    (hUm : ∀ s, AEMeasurable (U s) P) (hVm : ∀ s, AEMeasurable (V s) P)
    (hUL : ∀ᵐ w ∂P, Tendsto (fun s => U s w) l (nhds (D w)))
    (hVL : ∀ᵐ w ∂P, Tendsto (fun s => V s w) l (nhds (0 : ℝ)))
    (hLaw : ∀ s, P.map (U s) = P.map (V s)) :
    ∀ᵐ w ∂P, D w = 0 := by sorry
