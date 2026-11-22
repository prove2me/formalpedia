-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormulaCutoff_exists_globalBound_cutoffFun_u2082__p2m_749cad79fcd6
-- name    : LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun_u2082__p2m_749cad79fcd6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T09:07:41.300145+00:00
-- url     : https://prove2.me/theorems/af44b4d3-38d1-47c2-a1a6-b3115674844a
-- title:
--   exists globalBound cutoffFun₂
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂` is extracted from `LevyStochCalc.Ito.CutoffGlobalBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Global bounds on the derivatives of a cut-off state function

A `C²` function of time and state multiplied by the time–space cut-off of radius `R` vanishes
outside the closed ball of radius `2R`, and so do its time derivative, gradient and Hessian: a
function vanishing on an open set has vanishing derivatives there. Each of the three is
continuous, so each is bounded on that closed ball, hence bounded everywhere by the same
constant.

## Main statements

* `timeDeriv_cutoffFun₂_eq_zero`, `gradient_cutoffFun₂_eq_zero`, `hessian_cutoffFun₂_eq_zero` —
  the derivatives of the cut-off vanish outside the closed ball of radius `2R`.
* `exists_globalBound_cutoffFun₂` — one constant bounds the time derivative, every gradient entry
  and every Hessian entry of the cut-off of a `C²` function, at every time and every state.
-/

open Filter Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

open LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun_u2082__p2m_749cad79fcd6 (hu : ContDiff ℝ 2 (Function.uncurry u)) {R : ℝ}
    (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ s x, |timeDeriv (cutoffFun₂ u R) s x| ≤ K) ∧
      (∀ s x i, |gradient (cutoffFun₂ u R) s x i| ≤ K) ∧
      (∀ s x i j, |hessian (cutoffFun₂ u R) s x i j| ≤ K) := by sorry
