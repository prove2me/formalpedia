-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_eval_sq
-- name    : LevyStochCalc.Brownian.Ito.integral_eval_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:49:15.041247+00:00
-- url     : https://prove2.me/theorems/b5d209c7-7a4e-425d-8f66-d7c7f8f49109
-- title:
--   integral eval sq
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_eval_sq` is extracted from `LevyStochCalc.Brownian.ItoSimpleIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô isometry on simple predictable integrands

Expanding the square of the elementary integral into its diagonal and off-diagonal terms gives,
for an adapted simple predictable integrand `H` and a scalar Brownian motion `W`,
`E[(∫_0^T H dW) ^ 2] = ∑_i (t_{i+1} - t_i) · E[ξ_i ^ 2]`; combined with the energy of the
integrand this is the L²-isometry `E[(∫_0^T H dW) ^ 2] = ∫_0^T E[(H.eval s) ^ 2] ds`, stated
both for the lower integral and for the Bochner integral.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.integral_eval_sq {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2 := by sorry
