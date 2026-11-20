-- Prove2me | Theorems.Thm_LevyStochCalc_eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
-- name    : LevyStochCalc.eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:46:37.374589+00:00
-- url     : https://prove2.me/theorems/9e62d870-d3bc-47dc-8045-74e5ea084fa5
-- title:
--   eLpNorm tendsto of eLpNorm sub tendsto zero
-- statement:
--   The source theorem `LevyStochCalc.eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero` is extracted from `LevyStochCalc.Basic`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Basic_F000

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

theorem _root_.LevyStochCalc.eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f : α → E} {fn : ℕ → α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (h_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n - f) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n) p μ) Filter.atTop
      (nhds (MeasureTheory.eLpNorm f p μ)) := by sorry
