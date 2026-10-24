-- Prove2me | Theorems.Thm_LevyStochCalc_abs_taylorRemainderNormed_le_affine_408915f
-- name    : LevyStochCalc.abs_taylorRemainderNormed_le_affine_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:49:35.071462+00:00
-- url     : https://prove2.me/theorems/40db5bc2-6fa8-40a8-8001-ac8653bb8a9e
-- title:
--   Telescoped Taylor Remainder Along A Sequence
-- statement:
--   This theorem bounds the accumulated second-order Taylor remainder along a finite sequence. Let E, f, f′, f″, A, and K satisfy the same normed-space differentiability and nonnegativity assumptions as in `abs_sub_taylor_two_le_affine`, including ‖f″(z) − f″(w)‖ ≤ A + K‖z − w‖. For a sequence x : ℕ → E and m : ℕ, the definition `taylorRemainderNormed` satisfies
--
--   $$|\operatorname{taylorRemainderNormed}(f,f',f'',x,m)|\le A\sum_{i<m}\|x_{i+1}-x_i\|^2+K\sum_{i<m}\|x_{i+1}-x_i\|^3.$$
--
--   This is the telescoped form of the pointwise affine-modulus estimate and is suited to discretized paths and finite partitions.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L166-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_taylorRemainderNormed_le_affine`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LevyStochCalc.abs_taylorRemainderNormed_le_affine_408915f {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
    |taylorRemainderNormed f f' f'' x m|
      ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
        + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3 := by sorry
