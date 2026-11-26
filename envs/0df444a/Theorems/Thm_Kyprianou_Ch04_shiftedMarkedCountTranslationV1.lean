-- Prove2me | Theorems.Thm_Kyprianou_Ch04_shiftedMarkedCountTranslationV1
-- name    : Kyprianou.Ch04.shiftedMarkedCountTranslationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:41.673156+00:00
-- url     : https://prove2.me/theorems/0c2eebb0-50f0-571b-958d-9a3c28124908
-- title:
--   Translation of marked path count to relative time
-- statement:
--   Translation of marked path count to relative time
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem shiftedMarkedCountTranslationV1 {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω)
    (hX : Measurable (fun t => X t ω)) (hL : Measurable (fun t => L t ω))
    (s T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) :
    Kyprianou.Ch04.pathJumpMeasure X L ω (Ioc (s : ℝ) ((s+T : NNReal) : ℝ) ×ˢ B) =
      ({v : NNReal | 0 < v ∧ v ≤ T ∧ X (s+v) ω ≠ L (s+v) ω ∧
        X (s+v) ω - L (s+v) ω ∈ B}).encard := by
  sorry
end Kyprianou.Ch04
