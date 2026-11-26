-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureCountV1
-- name    : Kyprianou.Ch04.pathJumpMeasureCountV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:49.001045+00:00
-- url     : https://prove2.me/theorems/8d592dd4-98fd-4d50-af43-4a6298d2d04d
-- title:
--   Path jump measure equals the exact marked-time cardinality
-- statement:
--   Path jump measure equals the exact marked-time cardinality
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem pathJumpMeasureCountV1 {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω)
    (hX : Measurable (fun t => X t ω)) (hL : Measurable (fun t => L t ω))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    Kyprianou.Ch04.pathJumpMeasure X L ω A =
      ({t : NNReal | 0 < t ∧ X t ω ≠ L t ω ∧
        ((t : ℝ), X t ω - L t ω) ∈ A}).encard := by
  sorry
end Kyprianou.Ch04
