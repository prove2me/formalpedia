-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectedSignedFutureSupVersionV1
-- name    : Kyprianou.Ch03.reflectedSignedFutureSupVersionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:04:21.884844+00:00
-- url     : https://prove2.me/theorems/3244bc1e-f9ff-4372-b50f-a5f512fe6f47
-- title:
--   Measurable countable future supremum functional agreeing on original and restarted paths
-- statement:
--   Use the supremum of positive parts of signed path coordinates over a countable dense grid clipped at t, taking the ENNReal supremum and toReal. All good paths start at zero, are right-continuous and bounded on compact intervals, including all restarted paths, so the countable supremum agrees with the running supremum.
-- source:
--   Kyprianou (2006), Exercise 3.2: reflected Lévy processes are strong Markov.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectedSignedFutureSupVersionV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (c : ℝ) (r : Omega → NNReal) (t : NNReal) :
    ∃ H : (NNReal → ℝ) → ℝ, Measurable H ∧
      (∀ᵐ w ∂P, H (fun u => X u w) =
        LevyExtrema.SBA.runSup (fun u => c * X u w) t) ∧
      (∀ᵐ w ∂P, H (fun u => X (r w + u) w - X (r w) w) =
        LevyExtrema.SBA.runSup (fun u => c * (X (r w + u) w - X (r w) w)) t) := by
  sorry
