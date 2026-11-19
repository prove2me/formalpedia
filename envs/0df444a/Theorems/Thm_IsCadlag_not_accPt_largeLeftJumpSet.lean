-- Prove2me | Theorems.Thm_IsCadlag_not_accPt_largeLeftJumpSet
-- name    : IsCadlag.not_accPt_largeLeftJumpSet
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T22:13:53.679662+00:00
-- url     : https://prove2.me/theorems/8cb11423-b920-41b9-b692-f5919e0cd517
-- title:
--   not accPt largeLeftJumpSet
-- statement:
--   The source theorem `IsCadlag.not_accPt_largeLeftJumpSet` is extracted from `BrownianMotion.StochasticIntegral.Cadlag`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-! # cadlag functions

-/

@[expose] public section

open Filter TopologicalSpace Bornology
open scoped Topology ENNReal

variable {ι E : Type*} [TopologicalSpace ι]

section Jump

theorem IsCadlag.not_accPt_largeLeftJumpSet [LinearOrder ι] [OrderTopology ι] [UniformSpace E]
    {f : ι → E} (hf : IsCadlag f) {v : Set (E × E)} (hv : v ∈ uniformity E) (t : ι) :
    ¬ AccPt t (𝓟 (largeLeftJumpSet f v)) := by sorry
