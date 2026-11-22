-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormulaCutoff_exists_globalBound_cutoffFun_u2082__c12_p2m_e4ab12abdaa0
-- name    : LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun_u2082__c12_p2m_e4ab12abdaa0
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:40:56.268008+00:00
-- url     : https://prove2.me/theorems/fd6d26d6-ffc3-488c-b9a9-5a3b0bb204f1
-- title:
--   exists globalBound cutoffFun₂ c12
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂_c12` is extracted from `LevyStochCalc.Ito.CutoffC12`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuityC12_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The time–space cut-off of a `C^{1,2}` state function

The time–space cut-off of radius `R` multiplies a state function by a jointly `C²` factor, so the
cut-off of a `C^{1,2}` function is again of class `C^{1,2}`. Its time derivative, gradient and
Hessian vanish outside the closed ball of radius `2R` and are continuous, hence are bounded
everywhere by one constant. Along a path confined to a ball the cut-off leaves the jump side of
the Itô–Lévy formula — the compensated integral of the jump increment plus the compensator-drift
integral — unchanged, and that transfer needs of the state function only the joint continuity of
the function and of its cut-off.

## Main statements

* `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂_c12` — one constant bounds
  the time derivative, every gradient entry and every Hessian entry of the cut-off of a `C^{1,2}`
  function, at every time and every state.
* `LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun₂_eq_c12` — for a `C^{1,2}` state function
  the jump side is unchanged by the cut-off on the event that the path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormulaCutoff

open LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun_u2082__c12_p2m_e4ab12abdaa0 (hu : IsC12 u) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ s x, |timeDeriv (cutoffFun₂ u R) s x| ≤ K) ∧
      (∀ s x i, |gradient (cutoffFun₂ u R) s x i| ≤ K) ∧
      (∀ s x i j, |hessian (cutoffFun₂ u R) s x i j| ≤ K) := by sorry
