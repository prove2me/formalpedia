-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MeasurableJumpSubsetCountV1
-- name    : Kyprianou.Ch04.exercise46MeasurableJumpSubsetCountV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:48:01.553193+00:00
-- url     : https://prove2.me/theorems/9454f600-2433-46b8-bc27-0f5b05cf37b8
-- title:
--   Counting a jointly measurable subset of physical jump times is measurable
-- statement:
--   Use the existing s-finite intrinsic marked jump kernel. Its evaluation on the measurable section obtained by ignoring the mark equals the count of the selected jump times.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MeasurableJumpSubsetCountV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (S : Set (Omega × NNReal)) (hS : MeasurableSet S)
    (hJ : ∀ w t, (w,t) ∈ S → 0 < t ∧
      L.X t w - Function.leftLim (fun u : NNReal => L.X u w) t ≠ 0) :
    Measurable (fun w : Omega => (({t : NNReal | (w,t) ∈ S}).encard : ENNReal)) := by
  sorry
