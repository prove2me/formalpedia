-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_zero_of_regular_addContent
-- name    : MeasureTheory.tendsto_zero_of_regular_addContent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:30:45.246804+00:00
-- url     : https://prove2.me/theorems/2e5f228f-1170-4723-93a2-6f2b182d0683
-- title:
--   tendsto zero of regular addContent
-- statement:
--   The source theorem `MeasureTheory.tendsto_zero_of_regular_addContent` is extracted from `KolmogorovExtension4.RegularContent`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_KolmogorovExtension4_CompactSystem_F000
import Mathlib.MeasureTheory.Measure.AddContent

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}

-- `innerRegular` is defined only for a measure, hence we expand the definition to use it with a
-- content

theorem _root_.MeasureTheory.tendsto_zero_of_regular_addContent (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hs : ∀ n, s n ∈ R) (hs_anti : Antitone s) (hs_Inter : (⋂ n, s n) = ∅)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A (_ : A ∈ R) (ε : ℝ≥0∞) (_ : 0 < ε), ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε) :
    Filter.Tendsto (fun n ↦ m (s n)) Filter.atTop (nhds 0) := by sorry
