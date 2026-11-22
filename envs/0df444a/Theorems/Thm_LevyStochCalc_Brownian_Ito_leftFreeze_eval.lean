-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_leftFreeze_eval
-- name    : LevyStochCalc.Brownian.Ito.leftFreeze_eval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T18:52:10.10796+00:00
-- url     : https://prove2.me/theorems/67acf95a-63b4-4eed-979a-9430dccd6e6e
-- title:
--   leftFreeze eval
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.leftFreeze_eval` is extracted from `LevyStochCalc.Brownian.LeftFreeze`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Freezing a bounded adapted process at the left endpoints of a dyadic grid

Freezing a bounded adapted process `Y` at the left endpoints of the dyadic partition of `[0, t]`
of level `n` (`Analysis/DyadicGrid.lean`) gives a simple predictable integrand
`leftFreeze Y t n`, whose value at a time `s ∈ (0, t]` is `Y` at the left endpoint `leftPt t n s`
of the cell containing `s`. When the
frozen values converge, at every positive time and almost every sample point, to a bounded
process `Y₋`, the Itô integrals of `leftFreeze Y t n · H` converge in `L²` to the Itô integral of
`Y₋ · H`, by the difference isometry and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

open LevyStochCalc.Analysis

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Freeze

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t) (n : ℕ)

theorem _root_.LevyStochCalc.Brownian.Ito.leftFreeze_eval {s : ℝ} (hs : 0 < s) (hst : s ≤ t) (ω : Ω) :
    (leftFreeze Y hYb hYm ht n).eval s ω = Y (leftPt t n s) ω := by sorry
