-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_abs_clamp_sub_le
-- name    : LevyStochCalc.Brownian.Ito.abs_clamp_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:08:36.069579+00:00
-- url     : https://prove2.me/theorems/931eb759-d2c7-410d-a946-fec9cd1a792e
-- title:
--   abs clamp sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.abs_clamp_sub_le` is extracted from `LevyStochCalc.Brownian.ItoFourthMomentLintegral`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Fourth moment of the `L²` Itô integral

Truncation of a simple integrand and the `lintegral` form of the fourth-moment bound. Clamping
the coefficients to `[-C, C]` (`SimplePredictable.truncate`) moves a value no further from a
target already in `[-C, C]`, so a truncated approximant is still an approximant; the bound for
the simple integrands then passes to the `L²` Itô integral of any integrand bounded by `C` by
Fatou along an almost-everywhere convergent subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.abs_clamp_sub_le {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by sorry
