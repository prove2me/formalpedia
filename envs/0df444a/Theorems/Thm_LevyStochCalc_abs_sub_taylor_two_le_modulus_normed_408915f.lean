-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_modulus_normed_408915f
-- name    : LevyStochCalc.abs_sub_taylor_two_le_modulus_normed_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:49:35.236464+00:00
-- url     : https://prove2.me/theorems/b52d5fcb-9062-473f-8616-344678f828a8
-- title:
--   Normed-Space Second-Order Taylor Remainder Bound
-- statement:
--   This is the normed-space version of the second-order Taylor remainder estimate. Let E be a normed additive commutative group and real normed space, let f : E → ℝ, let f′ : E → E →L[ℝ] ℝ, let f″ : E → E →L[ℝ] E →L[ℝ] ℝ, and let M ≥ 0. Assume f and f′ have the indicated Fréchet derivatives at every point. For x, y : E, assume that every z in the segment joining x and y satisfies ‖f″(z) − f″(x)‖ ≤ M. Then, using `abs_sub_taylor_two_le_modulus_normed`,
--
--   $$|f(y)-f(x)-f'(x)(y-x)-\tfrac12 f''(x)(y-x)(y-x)|\le M\|y-x\|^2.$$
--
--   The result is dimension-free at the level of arbitrary normed spaces and isolates the dependence on the second-derivative oscillation along one segment.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L98-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_sub_taylor_two_le_modulus_normed`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.abs_sub_taylor_two_le_modulus_normed_408915f {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {x y : E}
    (hM : ∀ z ∈ segment ℝ x y, ‖f'' z - f'' x‖ ≤ M) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2| ≤ M * ‖y - x‖ ^ 2 := by sorry
