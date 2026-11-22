-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_le_clipTime_iff
-- name    : LevyStochCalc.Brownian.Ito.le_clipTime_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:42:00.893194+00:00
-- url     : https://prove2.me/theorems/994d4951-8f4f-4a38-880d-528cbe91c89e
-- title:
--   le clipTime iff
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.le_clipTime_iff` is extracted from `LevyStochCalc.Brownian.VectorItoStopped`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

theorem _root_.LevyStochCalc.Brownian.Ito.le_clipTime_iff {s : ℝ} (hs : s ≤ t) :
    ((s : ℝ) : WithTop ℝ) ≤ τ ω ↔ s ≤ clipTime τ t ω := by sorry
