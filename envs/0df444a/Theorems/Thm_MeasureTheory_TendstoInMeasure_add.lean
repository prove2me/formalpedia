-- Prove2me | Theorems.Thm_MeasureTheory_TendstoInMeasure_add
-- name    : MeasureTheory.TendstoInMeasure.add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:37:18.600198+00:00
-- url     : https://prove2.me/theorems/fb351950-5d27-494f-af32-56800c2f8649
-- title:
--   add
-- statement:
--   The source theorem `MeasureTheory.TendstoInMeasure.add` is extracted from `BrownianMotion.Auxiliary.ConvergenceInMeasure`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-! # Convergence in probability -/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem _root_.MeasureTheory.TendstoInMeasure.add {ι E : Type*} [NormedAddCommGroup E]
    {f g : ι → Ω → E} {l₁ l₂ : Ω → E} {u : Filter ι}
    (hf : TendstoInMeasure μ f u l₁) (hg : TendstoInMeasure μ g u l₂) :
    TendstoInMeasure μ (fun n ω ↦ f n ω + g n ω) u (fun ω ↦ l₁ ω + l₂ ω) := by sorry
