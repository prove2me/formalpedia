-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_eval_sq_clamped
-- name    : LevyStochCalc.Brownian.Ito.lintegral_eval_sq_clamped
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T16:46:51.178452+00:00
-- url     : https://prove2.me/theorems/b7f87c32-7308-46bd-932d-cddbabaf45d9
-- title:
--   lintegral eval sq clamped
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_eval_sq_clamped` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_eval_sq_clamped {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i : Fin H.N,
        ENNReal.ofReal (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
          * (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 := by sorry
