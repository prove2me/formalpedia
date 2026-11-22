-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_abs_mixedDriftIntegrand_le
-- name    : LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T10:14:02.000093+00:00
-- url     : https://prove2.me/theorems/96d908e9-c443-417e-9b80-c45454760b3b
-- title:
--   abs mixedDriftIntegrand le
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le` is extracted from `LevyStochCalc.Ito.ItoLevyMixedBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpPathBridge_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuity_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixed_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaTaylorBounds_F000
import Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F001
import Definitions.Def_LevyStochCalc_Ito_SubsequenceBookkeeping_F000
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le (coeffs : JumpDiffusionCoeffs n d E) {K₀ K₁ K₂ : ℝ}
    (hK₂0 : 0 ≤ K₂) (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (s : ℝ) (y x : Fin n → ℝ) :
    |mixedDriftIntegrand u coeffs s y x|
      ≤ K₀ + K₁ * ∑ p, |coeffs.μ s x p|
        + (1 / 2) * K₂ * ∑ p, ∑ q, ∑ j, (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 := by sorry
