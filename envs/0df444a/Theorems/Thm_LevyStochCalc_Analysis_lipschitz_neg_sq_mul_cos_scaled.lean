-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_lipschitz_neg_sq_mul_cos_scaled
-- name    : LevyStochCalc.Analysis.lipschitz_neg_sq_mul_cos_scaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:15:34.126818+00:00
-- url     : https://prove2.me/theorems/c9b5c008-822f-40fb-a2f5-534b296cc116
-- title:
--   lipschitz neg sq mul cos scaled
-- statement:
--   The source theorem `LevyStochCalc.Analysis.lipschitz_neg_sq_mul_cos_scaled` is extracted from `LevyStochCalc.Analysis.ScaledTrig`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_ScaledTrig_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The scaled cosine and sine

`x ↦ cos (l * x)` and `x ↦ sin (l * x)` are twice differentiable with derivatives bounded by
`|l|` and `l ^ 2`, and second derivatives Lipschitz with constant `|l| ^ 3` — the hypotheses of
Itô's formula for a scalar Itô process.
-/

namespace LevyStochCalc.Analysis

open Real

variable (l : ℝ)

theorem _root_.LevyStochCalc.Analysis.lipschitz_neg_sq_mul_cos_scaled (u v : ℝ) :
    |-l ^ 2 * Real.cos (l * u) - -l ^ 2 * Real.cos (l * v)| ≤ |l| ^ 3 * |u - v| := by sorry
