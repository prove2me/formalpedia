-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_eval_mul_on_common
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:41:11.595017+00:00
-- url     : https://prove2.me/theorems/7ee77b93-9f00-481c-8c39-573a7131f3e2
-- title:
--   eval mul on common
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common` is extracted from `LevyStochCalc.Brownian.ItoAlgebraProduct`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.mul_on_common H₂ h_eq).eval s ω = H₁.eval s ω * H₂.eval s ω := by sorry
