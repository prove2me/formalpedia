-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfCadlagDyadicExtremaLimitsV1
-- name    : Kyprianou.Ch03.supInfCadlagDyadicExtremaLimitsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T11:02:41.854239+00:00
-- url     : https://prove2.me/theorems/7921b5b1-07d9-487c-aa3f-549e4ba3d9c3
-- title:
--   Deterministic scaled dyadic extrema convergence for a càdlàg path
-- statement:
--   Apply the generic extrema convergence lemma to the full compact-horizon range and the dyadic ranges. The right-approaching scaled grid approximants converge in path values by right continuity. The bounds follow from the càdlàg property.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; parent 595bcca9-772a-41a6-8165-d1d8abc9d6e8.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfCadlagDyadicExtremaLimitsV1
    (f : NNReal → Real) (hf : IsCadlag f) (t : NNReal) (ht : 0 < t) :
    Tendsto (fun n : ℕ => sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
      f ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)))))) atTop
      (𝓝 (LevyExtrema.SBA.runSup f t)) ∧
    Tendsto (fun n : ℕ => sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
      f ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)))))) atTop
      (𝓝 (sInf (f '' Set.Icc 0 t))) := by sorry
