-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectedSignedRestartAEV1
-- name    : Kyprianou.Ch03.reflectedSignedRestartAEV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T17:58:05.371025+00:00
-- url     : https://prove2.me/theorems/70e01328-87ed-4ccd-8e96-7d9cab45c43a
-- title:
--   Pathwise restart identity for a signed reflected Lévy process
-- statement:
--   The reflected state restarts by splitting its running maximum at the stopping clock, subtracting the clock level and using future signed increments. This holds simultaneously along each càdlàg path, including arbitrary clocks.
-- source:
--   Kyprianou (2006), Exercise 3.2, proof via strong Markov and the running-maximum restart identity.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectedSignedRestartAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (c y : ℝ) (hy : 0 ≤ y)
    (r : Omega → NNReal) (t : NNReal) :
    ∀ᵐ w ∂P,
      reflectedSup (fun s v => c * X s v) y (r w + t) w =
      max (reflectedSup (fun s v => c * X s v) y (r w) w)
        (LevyExtrema.SBA.runSup (fun s => c * (X (r w + s) w - X (r w) w)) t)
        - c * (X (r w + t) w - X (r w) w) := by sorry
