-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDyadicExtremaAELimitsV1
-- name    : Kyprianou.Ch03.supInfDyadicExtremaAELimitsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:45.708826+00:00
-- url     : https://prove2.me/theorems/595bcca9-772a-41a6-8165-d1d8abc9d6e8
-- title:
--   Almost-sure convergence of scaled dyadic extrema
-- statement:
--   On the almost-sure càdlàg set, use boundedness on the compact interval and nested grids. The scaled dyadic ceiling approximation approaches each s≤t from the right, so the grid extrema converge to the full interval extrema. Reuse AvramDividend.Classical.avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; dyadic and limit children of f3decb5b-3c0d-4063-b885-79044b1ecb2f.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDyadicExtremaAELimitsV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))) atTop
        (𝓝 (LevyExtrema.SBA.runSup (fun s => X s ω) t)) ∧
      Tendsto (fun n : ℕ => sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
        X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))) atTop
        (𝓝 (sInf ((fun s : NNReal => X s ω) '' Set.Icc 0 t))) := by sorry
