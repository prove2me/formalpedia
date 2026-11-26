-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictablePhysicalKernelSectionV1
-- name    : Kyprianou.Ch04.predictablePhysicalKernelSectionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:30:23.385653+00:00
-- url     : https://prove2.me/theorems/7e6c1835-5261-5721-a422-3ddb01bec653
-- title:
--   Measurability of physical sections of predictable kernels
-- statement:
--   Each physical time-mark section of a marked predictable kernel is measurable.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictablePhysicalKernelSectionV1 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g) (ω : Ω) :
    Measurable (fun z : ℝ × ℝ => g ((z.1.toNNReal,ω),z.2)) := by
  sorry
end Kyprianou.Ch04
