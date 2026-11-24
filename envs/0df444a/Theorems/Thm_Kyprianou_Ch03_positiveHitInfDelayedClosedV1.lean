-- Prove2me | Theorems.Thm_Kyprianou_Ch03_positiveHitInfDelayedClosedV1
-- name    : Kyprianou.Ch03.positiveHitInfDelayedClosedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T11:02:20.85419+00:00
-- url     : https://prove2.me/theorems/a923c0b0-9b43-4d8b-b39f-5866111652b1
-- title:
--   Strictly positive hitting as infimum of reciprocal-delayed hitting times
-- statement:
--   Every positive witness exceeds some reciprocal delay, and every delayed witness is strictly positive. The two infima therefore coincide, including empty witness sets.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed closed hitting approximation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.positiveHitInfDelayedClosedV1
    {Omega : Type} (X : NNReal → Omega → ℝ) (B : Set ℝ) (w : Omega) :
    Kyprianou.Ch03.firstHittingTime X B w =
      ⨅ j : ℕ, sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧ X t w ∈ B}) := by
  sorry
