-- Prove2me | Theorems.Thm_Kyprianou_Ch04_shiftedMarkedCountExtractorV1
-- name    : Kyprianou.Ch04.shiftedMarkedCountExtractorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:58:15.795963+00:00
-- url     : https://prove2.me/theorems/28d31834-c0db-46b7-9e09-05c06b23c48a
-- title:
--   Measurable extraction of actual future marked count from shifted path
-- statement:
--   Measurable extraction of actual future marked count from shifted path
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem shiftedMarkedCountExtractorV1 (s T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ G : (NNReal → ℝ) → ENNReal, Measurable G ∧
      ∀ {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω),
      (∀ t : NNReal, ContinuousWithinAt (fun u => X u ω) (Ici t) t) →
      (∀ t : NNReal, 0 < t → Tendsto (fun u => X u ω) (𝓝[<] t) (𝓝 (L t ω))) →
      Kyprianou.Ch04.pathJumpMeasure X L ω (Ioc (s : ℝ) ((s+T : NNReal) : ℝ) ×ˢ B) =
        G (fun v : NNReal => X (s+v) ω - X s ω) := by
  sorry
end Kyprianou.Ch04
