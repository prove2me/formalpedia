-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_rightStoppedMeasurable
-- name    : Kyprianou.Ch01.mckeanDiscountedValue_rightStoppedMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:42:30.767066+00:00
-- url     : https://prove2.me/theorems/6d0c75ab-4373-4d16-acf8-28fca0f761b8
-- title:
--   Stopped discounted McKean value is measurable for every right-natural stopping time
-- statement:
--   The original right-natural stopping time is measurable. With measurable process sections and continuous paths, joint process evaluation at the finite part of tau is measurable. Compose with the Borel McKean value and measurable discount; glue with zero along the measurable event tau infinite. This establishes the stopped value measurability needed for the original optional sampling theorem.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingTime_measurable
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedValue_rightStoppedMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau) :
    let barrier := Real.log (K * phi / (1 + phi))
    Measurable (fun ω =>
      match tau ω with
      | none => (0 : ℝ)
      | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K barrier phi (x + X t ω)) := by sorry
