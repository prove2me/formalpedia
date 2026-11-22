-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_energy_lt_top_of_bounded
-- name    : LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:51:46.607225+00:00
-- url     : https://prove2.me/theorems/f102a2d5-9094-448d-afa4-8b8be8429e7f
-- title:
--   energy lt top of bounded
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded` is extracted from `LevyStochCalc.Brownian.ItoCutoff`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded {K : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |K ω s| ≤ M) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
