-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_affine_408915f
-- name    : LevyStochCalc.abs_sub_taylor_two_le_affine_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:49:35.430045+00:00
-- url     : https://prove2.me/theorems/060ccbef-2134-4357-adf9-662a7161fdb8
-- title:
--   Affine Second-Derivative Taylor Remainder Bound
-- statement:
--   This theorem gives a second-order Taylor estimate under an affine oscillation bound. Let E be a real normed space, f : E → ℝ, f′ and f″ the first and second Fréchet derivative fields, and A, K : ℝ with A ≥ 0 and K ≥ 0. Assume f and f′ have the stated Fréchet derivatives everywhere, and assume
--
--   $$\|f''(z)-f''(w)\|\le A+K\|z-w\|$$
--
--   for all z, w : E. Then, for all x, y : E,
--
--   $$|f(y)-f(x)-f'(x)(y-x)-\tfrac12 f''(x)(y-x)(y-x)|\le A\|y-x\|^2+K\|y-x\|^3.$$
--
--   The declaration `abs_sub_taylor_two_le_affine` is useful when a uniform additive oscillation term and a Lipschitz term are available simultaneously.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L139-L164 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_sub_taylor_two_le_affine`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.abs_sub_taylor_two_le_affine_408915f {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x y : E) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2|
      ≤ A * ‖y - x‖ ^ 2 + K * ‖y - x‖ ^ 3 := by sorry
