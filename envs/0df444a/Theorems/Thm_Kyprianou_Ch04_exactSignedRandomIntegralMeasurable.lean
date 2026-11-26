-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exactSignedRandomIntegralMeasurable
-- name    : Kyprianou.Ch04.exactSignedRandomIntegralMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:39:19.290002+00:00
-- url     : https://prove2.me/theorems/85cd12fb-6258-4ee8-ae93-8ddb4be4b496
-- title:
--   Exact measurability of signed random integrals
-- statement:
--   Measurable positive and negative extended integrals give exact strong measurability of the signed Bochner integral including exceptional outcomes.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.6 and Exercises 4.3–4.4; supporting lemma.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
open scoped ENNReal Classical
set_option autoImplicit false

/-- Exact signed random-integral measurability, including nonintegrable outcomes. -/
theorem Kyprianou.Ch04.exactSignedRandomIntegralMeasurable
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (R : Omega → Measure E) (f : Omega → E → Real)
    (hf : ∀ w, Measurable (f w))
    (hLp : Measurable (fun w => ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂(R w)))
    (hLn : Measurable (fun w => ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂(R w))) :
    StronglyMeasurable (fun w => ∫ z, f w z ∂(R w)) := by
  sorry
