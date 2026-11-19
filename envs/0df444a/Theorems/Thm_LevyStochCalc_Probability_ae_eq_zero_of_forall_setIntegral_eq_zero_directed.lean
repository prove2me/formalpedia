-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_ae_eq_zero_of_forall_setIntegral_eq_zero_directed
-- name    : LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_directed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:30:46.98645+00:00
-- url     : https://prove2.me/theorems/b75581f2-6a2d-4dbc-a8eb-0b7eb469789e
-- title:
--   ae eq zero of forall setIntegral eq zero directed
-- statement:
--   The source theorem `LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_directed` is extracted from `LevyStochCalc.Probability.SetIntegralPiSystem`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_SetIntegralPiSystem_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing set integrals over a π-system

A function that integrates to zero over every set of a π-system integrates to zero over every
set of the σ-algebra that π-system generates, because the sets on which it integrates to zero
form a Dynkin system. If the function is also measurable for that σ-algebra, it vanishes.
-/

open MeasureTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem _root_.LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_directed {m m0 : MeasurableSpace α}
    (hm : m ≤ m0) {μ : Measure α} [IsFiniteMeasure μ] {ι : Type*} [Nonempty ι]
    {𝒢 : ι → MeasurableSpace α} (hdir : Directed (· ≤ ·) 𝒢) (hgen : m = ⨆ i, 𝒢 i)
    {f : α → E} (hf : Integrable f μ) (hfm : StronglyMeasurable[m] f)
    (h : ∀ i, ∀ s, MeasurableSet[𝒢 i] s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by sorry
