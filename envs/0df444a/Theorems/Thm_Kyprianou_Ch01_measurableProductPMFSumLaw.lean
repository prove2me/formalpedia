-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableProductPMFSumLaw
-- name    : Kyprianou.Ch01.measurableProductPMFSumLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:12:46.546116+00:00
-- url     : https://prove2.me/theorems/fea64724-444d-4b4a-bd63-dd9715ed13c7
-- title:
--   Measurable discrete independent product sum has PMF convolution law
-- statement:
--   If two natural-number-valued measurable maps on a probability space have given PMFs p and q, their independent sum on the product probability space has the PMF p.bind (fun n => q.map (fun m => n+m)). The proof identifies the pushforward laws with PMF.toMeasure using Measure.ext_of_singleton, applies Measure.prod_apply and lintegral_countable' to evaluate the sum, then matches PMF.bind_apply. This is the precise measurable building block for the AEMeasurable reverse Lamperti product convolution.
-- source:
--   Mathlib Measure.prod_apply, Measure.ext_of_singleton, PMF.toMeasure_apply_singleton, lintegral_countable' and PMF.bind_apply.

import Mathlib
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableProductPMFSumLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f g : Ω → ℕ) (hf : Measurable f) (hg : Measurable g)
    (p q : PMF ℕ)
    (hp : ∀ n : ℕ, Q {ω | f ω = n} = p n)
    (hq : ∀ n : ℕ, Q {ω | g ω = n} = q n)
    (k : ℕ) :
    (Q.prod Q) {z : Ω × Ω | f z.1 + g z.2 = k} =
      ((p.bind (fun n => q.map (fun m => n + m))) k) := by
  sorry
