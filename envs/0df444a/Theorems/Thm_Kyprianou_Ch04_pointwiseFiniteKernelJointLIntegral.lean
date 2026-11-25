-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pointwiseFiniteKernelJointLIntegral
-- name    : Kyprianou.Ch04.pointwiseFiniteKernelJointLIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:27:08.733802+00:00
-- url     : https://prove2.me/theorems/937d399f-6d77-483f-8d99-7f51b1cd4af5
-- title:
--   Joint nonnegative integration against a pointwise finite measurable random measure is measurable.
-- statement:
--   Joint nonnegative integration against a pointwise finite measurable random measure is measurable.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.6, printed page 97.; correction of the formalisation of 61a5bc8c-34e9-49c2-b76f-9c0e0650fed4. Corrects the remaining exceptional-outcome measurability defect in AdaptedV2.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem pointwiseFiniteKernelJointLIntegral
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (R : Omega → Measure E)
    (hR : ∀ S : Set E, MeasurableSet S → Measurable (fun w => R w S))
    (hFin : ∀ w, IsFiniteMeasure (R w))
    (f : Omega × E → ENNReal) (hf : Measurable f) :
    Measurable (fun w => ∫⁻ z, f (w,z) ∂(R w)) := by
  sorry
end Kyprianou.Ch04
