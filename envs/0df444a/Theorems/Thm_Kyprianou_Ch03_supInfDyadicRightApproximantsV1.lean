-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDyadicRightApproximantsV1
-- name    : Kyprianou.Ch03.supInfDyadicRightApproximantsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:31.721646+00:00
-- url     : https://prove2.me/theorems/0164a48d-e798-4e6c-8d5e-d2ab4d333213
-- title:
--   Every bounded time admits right-approaching scaled dyadic grid approximants
-- statement:
--   Reuse the proved scaled dyadic ceiling horizon limit. The ceiling of (s/t)*2^n is bounded by 2^n since s/t≤1, hence gives a valid finite index. Normalize the order of multiplication and division.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; parent 595bcca9-772a-41a6-8165-d1d8abc9d6e8.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDyadicRightApproximantsV1
    (s t : NNReal) (ht : 0 < t) (hs : s ≤ t) :
    ∃ u : ℕ → NNReal,
      (∀ n, s ≤ u n ∧ ∃ i : Fin (2 ^ n + 1),
        u n = (i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ∧
      Tendsto u atTop (𝓝 s) := by sorry
