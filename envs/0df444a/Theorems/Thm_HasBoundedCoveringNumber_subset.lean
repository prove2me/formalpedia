-- Prove2me | Theorems.Thm_HasBoundedCoveringNumber_subset
-- name    : HasBoundedCoveringNumber.subset
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:24:42.906432+00:00
-- url     : https://prove2.me/theorems/8c405637-420f-4b53-9697-e213a7d88572
-- title:
--   subset
-- statement:
--   The source theorem `HasBoundedCoveringNumber.subset` is extracted from `BrownianMotion.Continuity.HasBoundedInternalCoveringNumber`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

theorem HasBoundedCoveringNumber.subset {B : Set T}
    (h : HasBoundedCoveringNumber A c d) (hBA : B ⊆ A) (hd : 0 ≤ d) :
    HasBoundedCoveringNumber B (2 ^ d * c) d := by sorry
