-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_setIntegral_eval_sq_Icc_clamped
-- name    : LevyStochCalc.Poisson.Compensated.setIntegral_eval_sq_Icc_clamped
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T17:01:08.876187+00:00
-- url     : https://prove2.me/theorems/553a8dfd-98da-4e6d-b430-49c13ccc14e7
-- title:
--   setIntegral eval sq Icc clamped
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.setIntegral_eval_sq_Icc_clamped` is extracted from `LevyStochCalc.Poisson.CompensatedMartingaleIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F000

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

theorem _root_.LevyStochCalc.Poisson.Compensated.setIntegral_eval_sq_Icc_clamped
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t)).toReal
          * (φ.ξ i ω) ^ 2 := by sorry
