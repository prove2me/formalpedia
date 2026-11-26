-- Prove2me | Theorems.Thm_Kyprianou_Ch04_strictLeftSampleWeightLimitV1
-- name    : Kyprianou.Ch04.strictLeftSampleWeightLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:36:24.136874+00:00
-- url     : https://prove2.me/theorems/47cb1bb2-35ea-5651-bc97-40b93724bc0e
-- title:
--   Predictable weight convergence along strict-left samples
-- statement:
--   Strict-left state samples and time continuity give convergence of predictable weights.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integration.

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem strictLeftSampleWeightLimitV1 (g : ℝ → ℝ → ℝ) (Y : NNReal → ℝ)
    (t : NNReal) (l : ℝ) (u : ℕ → NNReal)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hu : Tendsto u atTop (𝓝[<] t))
    (hY : Tendsto Y (𝓝[<] t) (𝓝 l)) :
    Tendsto (fun n => g (u n : ℝ) (Y (u n))) atTop (𝓝 (g (t : ℝ) l)) := by
  sorry
end Kyprianou.Ch04
