-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_lintegral_sq_le_bieleckiNorm_sq
-- name    : LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_le_bieleckiNorm_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:48:00.228011+00:00
-- url     : https://prove2.me/theorems/253ca4a5-f6f3-4e6a-a937-523a12157b47
-- title:
--   lintegral lintegral sq le bieleckiNorm sq
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_le_bieleckiNorm_sq` is extracted from `LevyStochCalc.Ito.PicardOutputWeighting`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki weighting and the per-component difference bounds

The Bielecki norm with rate `β` dominates the second moment at each time of `[0, T]` after
reweighting by `e^{2βs}`, and the doubly-integrated energy over `[0, t]` by
`e^{2βt}/(2β)`, the factor `1/(2β)` being what makes the Picard rate small for large `β`.
Combined with the Lipschitz bounds on the coefficients this bounds the drift, diffusion and
jump components of the difference of two Picard steps by the energy of the difference of the
two frozen paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace E] in

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_le_bieleckiNorm_sq {β : ℝ} (hβ : 0 < β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
          * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by sorry
