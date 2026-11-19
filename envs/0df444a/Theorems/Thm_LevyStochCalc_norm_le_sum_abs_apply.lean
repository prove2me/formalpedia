-- Prove2me | Theorems.Thm_LevyStochCalc_norm_le_sum_abs_apply
-- name    : LevyStochCalc.norm_le_sum_abs_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:29:44.150901+00:00
-- url     : https://prove2.me/theorems/9685d965-7a57-4583-bde9-970fb4a335c2
-- title:
--   norm le sum abs apply
-- statement:
--   The source theorem `LevyStochCalc.norm_le_sum_abs_apply` is extracted from `LevyStochCalc.Brownian.CoordDerivative`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CoordDerivative_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Partial derivatives on `Fin n → ℝ`

A continuous linear functional on `Fin n → ℝ` is determined by its values on the standard basis
vectors `Pi.single p 1`, so the first- and second-order terms of a Taylor expansion split into
partial derivatives. The bounds and Lipschitz constants of those scalar functions come from the
operator norms of the Fréchet derivatives.

## Main statements

* `LevyStochCalc.clm_apply_pi` — expansion of a continuous linear map on `Fin n → ℝ`.
* `LevyStochCalc.coordDeriv`, `LevyStochCalc.coordDeriv₂` — the partial derivatives.
* `LevyStochCalc.apply_eq_sum_coordDeriv`, `LevyStochCalc.apply₂_eq_sum_coordDeriv₂` — the
  first- and second-order terms in coordinates.
* `LevyStochCalc.abs_coordDeriv_sub_le` — the Lipschitz bound of a partial derivative, from
  the bound on the second derivative.
-/

namespace LevyStochCalc

open ContinuousLinearMap

variable {n : ℕ}

section Expansion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Expansion

section Coord

variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}

theorem _root_.LevyStochCalc.norm_le_sum_abs_apply (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, |A (Pi.single p 1)| := by sorry
