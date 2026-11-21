-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_lintegral_sq_stopOf_le
-- name    : LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stopOf_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:22:13.247221+00:00
-- url     : https://prove2.me/theorems/e57ed472-c830-4358-9508-ed08bd7f0301
-- title:
--   lintegral lintegral sq stopOf le
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stopOf_le` is extracted from `LevyStochCalc.Ito.PicardBieleckiNorm`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stopOf_le {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ)) (hZm : Measurable (Function.uncurry Z)) (hT : 0 ≤ T)
    (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := by sorry
