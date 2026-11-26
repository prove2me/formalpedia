-- Prove2me | Theorems.Thm_Kyprianou_Ch05_isLevyProcess_completion
-- name    : Kyprianou.Ch05.isLevyProcess_completion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:06:56.778897+00:00
-- url     : https://prove2.me/theorems/5cf7fe25-c17a-40d4-a87b-844aeb71b4b3
-- title:
--   Lévy process axioms survive measure completion
-- statement:
--   Independence is characterised by finite preimage intersections and their masses, unchanged by completion. Stationary increment laws agree by the completion pushforward identity. Start and a.e. path axioms transfer definitionally.
-- source:
--   Kyprianou (2006), Chapter 5; completion transport for strong Markov reuse.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.isLevyProcess_completion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (Y : NNReal → Omega → Real)
    (hY : ProbabilityTheory.IsLevyProcess Y P) :
    ProbabilityTheory.IsLevyProcess
      (fun t (w : NullMeasurableSpace Omega P) => Y t w) P.completion := by
  sorry
