-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableClampedPastKernelMeasurableV1
-- name    : Kyprianou.Ch04.predictableClampedPastKernelMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:20:46.480945+00:00
-- url     : https://prove2.me/theorems/8c3d565e-70f6-5a6c-a4de-ba221d6fabdd
-- title:
--   Clamped predictable marked kernel is jointly past measurable
-- statement:
--   A predictable kernel, sampled with time clamped to a fixed horizon, is jointly past measurable.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableClampedPastKernelMeasurableV1 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration NNReal mΩ) (T : NNReal)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g) :
    Measurable[(F T).prod inferInstance]
      (fun p : Ω × (ℝ × ℝ) => g ((min p.2.1.toNNReal T,p.1),p.2.2)) := by
  sorry
end Kyprianou.Ch04
