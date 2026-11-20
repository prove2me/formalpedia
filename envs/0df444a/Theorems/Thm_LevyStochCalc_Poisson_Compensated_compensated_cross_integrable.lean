-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_compensated_cross_integrable
-- name    : LevyStochCalc.Poisson.Compensated.compensated_cross_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T17:07:50.408067+00:00
-- url     : https://prove2.me/theorems/cbbea466-a658-406a-b432-998e5e3742f8
-- title:
--   compensated cross integrable
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.compensated_cross_integrable` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

/-! ### Set-level quadratic-variation isometry

The increment squares onto the increment boxes; off-diagonal cross terms vanish
(independence + zero mean), and diagonal terms give the box intensities
(independence + `compensated_second_moment`). -/

theorem _root_.LevyStochCalc.Poisson.Compensated.compensated_cross_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBf : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => N.compensated B ω * N.compensated C ω) P := by sorry
