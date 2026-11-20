-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_sub_eq_increment_ae
-- name    : LevyStochCalc.Poisson.Compensated.simpleIntegral_sub_eq_increment_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T17:03:00.480385+00:00
-- url     : https://prove2.me/theorems/341d95b6-6f70-40dc-ba61-9ccfecce8ffe
-- title:
--   simpleIntegral sub eq increment ae
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_sub_eq_increment_ae` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Clamped compensator and increment boxes of the compensated simple integral

The compensator `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` of the quadratic variation in its explicit
clamped form `∑_i ν̂(timeRect i t) · ξᵢ²`, the a.e. decomposition of the increment
`simpleIntegral t − simpleIntegral s` over the increment rectangles
`timeRect i t \ timeRect i s` (each a clean box `Ioc a b ×ˢ Aᵢ`), and the box-level moment
identities behind the set-level isometry: independence of a future box increment from the
past, the weighted diagonal second moment, the vanishing of the weighted off-diagonal cross
terms, and cross-integrability of two compensated masses.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Clamped compensator

The compensator of the quadratic variation, `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds`, in its
explicit clamped form `∑_i (referenceIntensity ν (timeRect i t)) · ξᵢ²`. -/

/-! ### Increment decomposition

The increment `simpleIntegral t − simpleIntegral s` decomposes (a.e.) over the
increment rectangles `timeRect i t \ timeRect i s`, the basis for the set-level
quadratic-variation isometry. -/

theorem _root_.LevyStochCalc.Poisson.Compensated.simpleIntegral_sub_eq_increment_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {s t : ℝ} (hst : s ≤ t) :
    (fun ω => simpleIntegral N φ t ω - simpleIntegral N φ s ω)
      =ᵐ[P] fun ω => ∑ i : Fin φ.N,
        φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω := by sorry
