-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_timeRect_sdiff_eq_box
-- name    : LevyStochCalc.Poisson.Compensated.timeRect_sdiff_eq_box
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:04:33.644711+00:00
-- url     : https://prove2.me/theorems/42da6827-30de-443d-be57-ea0ab60e82a1
-- title:
--   timeRect sdiff eq box
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.timeRect_sdiff_eq_box` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F001

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

theorem _root_.LevyStochCalc.Poisson.Compensated.timeRect_sdiff_eq_box
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) {s t : ℝ} (hst : s ≤ t) :
    φ.timeRect i t \ φ.timeRect i s
      = Set.Ioc (max s (min (φ.partition i.castSucc) t))
          (max s (min (φ.partition i.succ) t)) ×ˢ φ.A i := by sorry
