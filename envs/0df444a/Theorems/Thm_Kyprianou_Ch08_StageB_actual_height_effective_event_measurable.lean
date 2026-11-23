-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_effective_event_measurable
-- name    : Kyprianou.Ch08.StageB.actual_height_effective_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T02:57:50.648182+00:00
-- url     : https://prove2.me/theorems/9977a4ec-637c-4542-8ae5-6d6072bbf453
-- title:
--   Theorem 8.2 effective two-sided-exit no-drawdown event is measurable
-- statement:
--   For a spectrally negative Levy process A with filtration F, and positive barrier b and drawdown height h, the event on which the two-sided exit-up time is finite and the path has no drawdown before upcrossing is measurable.
-- source:
--   Source-faithful decomposition Child A of parent Kyprianou.Ch08.StageB.actual_height_semigroup [47fdba96-7849-46b6-87b0-6cea26c5eadd], mission 774734e3-04f0-4425-85f7-4e268610a046, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474. Isolates measurability of the finite two-sided-upcrossing/no-drawdown event appearing in the Proved stageB_bpay_iSup record [42686235-3ca1-41e1-90ca-c5d3fc0e19f4]. Repair of publication job 6d91b001-1cd7-47c4-b15e-b686a10119e7: the invalid qualified constant Set.setOf is replaced by the pinned root constant setOf, and the declaration is explicitly root-qualified so the generated target self-reference resolves. The proposition and proof body do not mention the helper's own name. Preamble, imports, process type, positivity hypotheses and event are unchanged from the frozen failed spec.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal

theorem _root_.Kyprianou.Ch08.StageB.actual_height_effective_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (A : SpectrallyNegativeLevy P 𝓕) (b h : ℝ) (hb : 0 < b) (hh : 0 < h) :
    MeasurableSet (setOf (fun ω : Ω =>
      twoSidedExitUpTime A b ω < ⊤ ∧
        NoDrawdownBeforeUpcrossing A.X b h ω)) := by
  sorry
