-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_offDiagonal_increment_zero
-- name    : LevyStochCalc.Poisson.Compensated.offDiagonal_increment_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T17:05:55.335164+00:00
-- url     : https://prove2.me/theorems/fb74183f-10f9-4b2c-9610-0bb20dff6c56
-- title:
--   offDiagonal increment zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.offDiagonal_increment_zero` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Poisson.Compensated.offDiagonal_increment_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {i j : Fin φ.N} (hij : i < j)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition j.castSucc)) (φ.ξ j))
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ s) g)
    (h_genuine_j :
      max s (min (φ.partition j.castSucc) t) < max s (min (φ.partition j.succ) t)) :
    ∫ ω, g ω * ((φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω)
        * (φ.ξ j ω * N.compensated (φ.timeRect j t \ φ.timeRect j s) ω)) ∂P = 0 := by sorry
