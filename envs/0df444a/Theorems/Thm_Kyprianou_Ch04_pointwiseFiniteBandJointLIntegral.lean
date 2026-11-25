-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pointwiseFiniteBandJointLIntegral
-- name    : Kyprianou.Ch04.pointwiseFiniteBandJointLIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:27:15.694163+00:00
-- url     : https://prove2.me/theorems/d4b2e35a-c3c5-4e0c-8e63-28c88450806a
-- title:
--   Exhaust the measurable region by increasing pointwise finite bands; measurable finite-kernel integrals increase to the full integral.
-- statement:
--   Exhaust the measurable region by increasing pointwise finite bands; measurable finite-kernel integrals increase to the full integral.
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
theorem pointwiseFiniteBandJointLIntegral
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (R : Omega → Measure E) (U : Set E) (hU : MeasurableSet U)
    (B : Nat → Set E) (hB : ∀ n, MeasurableSet (B n))
    (hm : Monotone B) (hc : (⋃ n, B n) = U)
    (hR : ∀ S : Set E, MeasurableSet S → S ⊆ U → Measurable (fun w => R w S))
    (hFin : ∀ n w, R w (B n) ≠ ⊤)
    (f : Omega × E → ENNReal) (hf : Measurable f) :
    Measurable (fun w => ∫⁻ z in U, f (w,z) ∂(R w)) := by
  sorry
end Kyprianou.Ch04
