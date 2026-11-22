-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_excursion_tail_limits
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_excursion_tail_limits
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T15:14:44.725281+00:00
-- url     : https://prove2.me/theorems/b12465b4-d9ea-4fde-9079-a0d134fb3266
-- title:
--   Theorem 8.2 helper: one-sided continuity of finite excursion tails
-- statement:
--   For a measure whose closed upper tails are finite at every positive level, the real-valued closed-tail function tends from the left to the closed tail and from the right to the open tail. This gives the endpoint coefficients needed in Theorem 8.2's one-sided scale derivative proofs.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

theorem source_result8_2_v2_excursion_tail_limits
    (n : Measure ℝ)
    (hfin : ∀ h : ℝ, 0 < h → n (Set.Ici h) < ⊤) :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => (n (Set.Ici t)).toReal)
        (𝓝[<] x) (𝓝 ((n (Set.Ici x)).toReal)) ∧
      Tendsto (fun t : ℝ => (n (Set.Ici t)).toReal)
        (𝓝[>] x) (𝓝 ((n (Set.Ioi x)).toReal)) := by
  sorry

end Kyprianou.Ch08.StageB
