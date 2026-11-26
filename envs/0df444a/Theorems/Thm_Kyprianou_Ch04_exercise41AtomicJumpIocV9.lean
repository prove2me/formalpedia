-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41AtomicJumpIocV9
-- name    : Kyprianou.Ch04.exercise41AtomicJumpIocV9
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:30:12.218406+00:00
-- url     : https://prove2.me/theorems/53acaace-4ec0-5ff4-8b1d-abd40fbd45e4
-- title:
--   Absolute summability of the physical jump differences gives integrability and the exact open-left marked integral
-- statement:
--   Absolute summability of the physical jump differences gives integrability and the exact open-left marked integral
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41AtomicJumpIocV9
    {Ω : Type} [MeasurableSpace Ω]
    (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hNeg : ∀ s : NNReal, 0 < s → X s w ≤ Xleft s w)
    (hJ : Set.Countable {s : NNReal | 0 < s ∧ X s w ≠ Xleft s w})
    (t : NNReal)
    (g : ℝ → ℝ)
    (hs : Summable (fun s : Ioc (0 : NNReal) t => ‖g (X s w) - g (Xleft s w)‖)) :
    let μ := (pathJumpMeasure X Xleft w).restrict
        (Ioc (0 : ℝ) (t : ℝ) ×ˢ Iio (0 : ℝ))
    let J := fun z : ℝ × ℝ => g (Xleft z.1.toNNReal w + z.2) - g (Xleft z.1.toNNReal w)
    Integrable J μ ∧ (∫ z, J z ∂μ) =
      ∑' s : Ioc (0 : NNReal) t, (g (X s w) - g (Xleft s w)) := by
  sorry
