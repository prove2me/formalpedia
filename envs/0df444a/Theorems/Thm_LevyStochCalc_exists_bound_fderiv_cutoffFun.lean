-- Prove2me | Theorems.Thm_LevyStochCalc_exists_bound_fderiv_cutoffFun
-- name    : LevyStochCalc.exists_bound_fderiv_cutoffFun
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:47:57.824768+00:00
-- url     : https://prove2.me/theorems/853f92d9-a0b8-4870-8ed3-5974864f0975
-- title:
--   exists bound fderiv cutoffFun
-- statement:
--   The source theorem `LevyStochCalc.exists_bound_fderiv_cutoffFun` is extracted from `LevyStochCalc.Brownian.ItoCutoff`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

theorem _root_.LevyStochCalc.exists_bound_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) : ∃ K₁ : ℝ, ∀ z, ‖fderiv ℝ (cutoffFun f k) z‖ ≤ K₁ := by sorry
