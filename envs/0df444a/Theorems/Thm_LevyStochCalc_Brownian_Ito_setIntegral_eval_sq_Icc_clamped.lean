-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_setIntegral_eval_sq_Icc_clamped
-- name    : LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:04:21.569092+00:00
-- url     : https://prove2.me/theorems/8f007bca-d88f-47a9-9cdd-de80fb94d562
-- title:
--   setIntegral eval sq Icc clamped
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionCompensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped {T : ℝ} (G : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume
      = ∑ i : Fin G.N,
        (min (G.partition i.succ) t - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2 := by sorry
