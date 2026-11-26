-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RightContPhysicalMarkedKernelV1
-- name    : Kyprianou.Ch04.exercise46RightContPhysicalMarkedKernelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T23:36:50.734803+00:00
-- url     : https://prove2.me/theorems/72602558-49c2-4e1c-94a1-011c9ad84eee
-- title:
--   Physical marked jump kernel lifted to the right-continuous predictable sigma algebra
-- statement:
--   Lift the original Lévy process to its right-continuous filtration without changing its paths and apply the proved physical marked kernel measurability theorem.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RightContPhysicalMarkedKernelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    let NX : Omega → Measure (NNReal × Real) := fun w =>
      ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
        Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    let K : Omega → @Measure ((NNReal × Omega) × Real)
      (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
        (inferInstance : MeasurableSpace Real)) := fun w =>
      @Measure.map (NNReal × Real) ((NNReal × Omega) × Real) inferInstance
        (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
          (inferInstance : MeasurableSpace Real)) (fun p => ((p.1,w),p.2)) (NX w)
    AEMeasurable K P := by
  sorry
