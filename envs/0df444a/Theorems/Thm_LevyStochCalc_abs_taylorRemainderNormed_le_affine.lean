-- Prove2me | Theorems.Thm_LevyStochCalc_abs_taylorRemainderNormed_le_affine
-- name    : LevyStochCalc.abs_taylorRemainderNormed_le_affine
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T23:46:22.456781+00:00
-- url     : https://prove2.me/theorems/8b7f25f7-09ef-473b-ab21-885df9f148a0
-- title:
--   abs taylorRemainderNormed le affine
-- statement:
--   The source theorem `LevyStochCalc.abs_taylorRemainderNormed_le_affine` is extracted from `LevyStochCalc.Brownian.TaylorTwoModulus`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwoModulus_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The second-order Taylor bound against a modulus of continuity

A Lipschitz second derivative is more than the Taylor bound needs: the remainder is controlled by
the oscillation of the second derivative on the segment alone, which is what a merely continuous
second derivative supplies. The affine form `A + K‖z − w‖` of the oscillation bound covers a
Lipschitz second derivative (`A = 0`) and a merely uniformly continuous one (`K` chosen from the
modulus at scale `A`) in one statement.

## Main statements

* `LevyStochCalc.abs_sub_taylor_two_le_modulus_normed` — the bound by the oscillation on the
  segment.
* `LevyStochCalc.abs_sub_taylor_two_le_affine` — the bound `A‖y − x‖² + K‖y − x‖³` under an
  affine oscillation bound.
* `LevyStochCalc.abs_taylorRemainderNormed_le_affine` — its telescoped form along a sequence.
-/

namespace LevyStochCalc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem _root_.LevyStochCalc.abs_taylorRemainderNormed_le_affine {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
    |taylorRemainderNormed f f' f'' x m|
      ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
        + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3 := by sorry
