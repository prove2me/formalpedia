-- Prove2me | Theorems.Thm_LevyStochCalc_abs_coordDeriv_u2082__sub_le_affine_p2m_9e8c1965c746
-- name    : LevyStochCalc.abs_coordDeriv_u2082__sub_le_affine_p2m_9e8c1965c746
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:30:30.028193+00:00
-- url     : https://prove2.me/theorems/fcec597e-2146-4fae-b831-f19b03dd84b9
-- title:
--   abs coordDeriv₂ sub le affine
-- statement:
--   The source theorem `LevyStochCalc.abs_coordDeriv₂_sub_le_affine` is extracted from `LevyStochCalc.Brownian.CoordDerivative`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.abs_coordDeriv_u2082__sub_le_affine_p2m_9e8c1965c746 {A K : ℝ} (h : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (p q : Fin n) (x y : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y| ≤ A + K * ‖x - y‖ := by sorry
