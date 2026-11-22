-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_indIoc_lt_top
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_indIoc_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T18:52:25.822459+00:00
-- url     : https://prove2.me/theorems/eeab95c7-d93e-4e78-b1f9-eb8c8bcb7ed1
-- title:
--   lintegral sq indIoc lt top
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_indIoc_lt_top` is extracted from `LevyStochCalc.Brownian.ItoIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô integral of an indicator is a Brownian increment

The integrand `1_{(a, b]}` is simple, so its `L²` Itô integral up to a time `t` is the elementary
integral `W_{b ∧ t} − W_{a ∧ t}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Indicator

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_sq_indIoc_lt_top (P : Measure Ω) [IsProbabilityMeasure P] (a b : ℝ)
    (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
