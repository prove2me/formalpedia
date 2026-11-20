-- Prove2me | Theorems.Thm_LevyStochCalc_lintegral_sq_eq_eLpNorm_sq_on_triple_prod
-- name    : LevyStochCalc.lintegral_sq_eq_eLpNorm_sq_on_triple_prod
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:47:32.825025+00:00
-- url     : https://prove2.me/theorems/6891b9b0-4f18-4d83-b7de-133b527f5422
-- title:
--   lintegral sq eq eLpNorm sq on triple prod
-- statement:
--   The source theorem `LevyStochCalc.lintegral_sq_eq_eLpNorm_sq_on_triple_prod` is extracted from `LevyStochCalc.Basic`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Basic_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# LevyStochCalc.Basic

Common imports plus small L² helper lemmas shared across the library:
`eLpNorm` reverse-triangle / difference bounds and L²-continuity (Bochner-L²
limit) lemmas in the plain, Brownian, and compensated-Poisson integrand shapes.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

theorem _root_.LevyStochCalc.lintegral_sq_eq_eLpNorm_sq_on_triple_prod
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {η : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite η]
    (h : α × β × γ → ℝ) (hh : Measurable h) :
    ∫⁻ x, ∫⁻ y, ∫⁻ z, (‖h (x, y, z)‖₊ : ℝ≥0∞) ^ 2 ∂η ∂ν ∂μ
      = MeasureTheory.eLpNorm h 2 (μ.prod (ν.prod η)) ^ (2 : ℝ) := by sorry
