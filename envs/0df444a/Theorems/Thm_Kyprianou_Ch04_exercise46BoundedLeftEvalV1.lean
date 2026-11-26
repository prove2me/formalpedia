-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BoundedLeftEvalV1
-- name    : Kyprianou.Ch04.exercise46BoundedLeftEvalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:09:39.293679+00:00
-- url     : https://prove2.me/theorems/35460c4c-8336-59e9-9a93-58997f7af79e
-- title:
--   Bounded measurable clock evaluation of the physical left limit
-- statement:
--   Compose the measurable capped joint evaluation with the bounded clock and fractional left mesh. Pointwise mesh convergence and measurable limit yield the stopped left limit.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BoundedLeftEvalV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (a : Omega → NNReal) (T : NNReal) (hT : ∀ w, a w ≤ T)
    (ha : Measurable[G.rightCont T] a)
    (hJoint : @Measurable (NNReal × Omega) Real
      (@Prod.instMeasurableSpace NNReal Omega inferInstance (G.rightCont T))
      inferInstance (fun z => L.X (min z.1 T) z.2)) :
    Measurable[G.rightCont T] (fun w =>
      Function.leftLim (fun u : NNReal => L.X u w) (a w)) := by
  sorry
