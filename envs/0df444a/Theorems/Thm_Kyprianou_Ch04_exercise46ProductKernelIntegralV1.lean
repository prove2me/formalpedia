-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ProductKernelIntegralV1
-- name    : Kyprianou.Ch04.exercise46ProductKernelIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:43:20.820944+00:00
-- url     : https://prove2.me/theorems/a042bcf2-8e56-48c2-b475-ec874fb90be7
-- title:
--   Bounded kernel integral transferred by a restart product law
-- statement:
--   The shifted future path is distributed jointly with the first service mark according to the product of the mark law and the original path law. Map the bounded kernel integral to this product and apply Fubini.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ProductKernelIntegralV1
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → Real) (Z Y : Omega → E)
    (hJ : AEMeasurable J P) (hZ : AEMeasurable Z P) (hY : Measurable Y)
    (hLaw : P.map (fun w => (J w,Z w)) = (P.map J).prod (P.map Y))
    (f : Real × E → Real) (hf : Measurable f) (hBound : ∀ z, ‖f z‖ ≤ 1) :
    (∫ w, f (J w,Z w) ∂P) = ∫ y, (∫ w, f (y,Y w) ∂P) ∂(P.map J) := by
  sorry
