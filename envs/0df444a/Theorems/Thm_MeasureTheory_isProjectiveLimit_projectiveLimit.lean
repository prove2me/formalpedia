-- Prove2me | Theorems.Thm_MeasureTheory_isProjectiveLimit_projectiveLimit
-- name    : MeasureTheory.isProjectiveLimit_projectiveLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:41:22.051227+00:00
-- url     : https://prove2.me/theorems/3358b377-f2ab-4817-a9d9-abb5f749c02d
-- title:
--   isProjectiveLimit projectiveLimit
-- statement:
--   The source theorem `MeasureTheory.isProjectiveLimit_projectiveLimit` is extracted from `KolmogorovExtension4.KolmogorovExtension`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_KolmogorovExtension4_KolmogorovExtension_F000

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

section InnerRegular

variable [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

local notation "Js" => measurableCylinders.finset

local notation "As" => measurableCylinders.set

end InnerRegular

section Polish

variable [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ I, IsFiniteMeasure (P I)]

theorem _root_.MeasureTheory.isProjectiveLimit_projectiveLimit (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimit P hP) P := by sorry
