-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_modulus_408915f
-- name    : LevyStochCalc.abs_sub_taylor_two_le_modulus_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:49:37.546347+00:00
-- url     : https://prove2.me/theorems/018605c8-bff4-4a55-ba5a-1eef0dba4fc6
-- title:
--   Real Second-Order Taylor Remainder Bound
-- statement:
--   This is a second-order Taylor remainder estimate for a twice differentiable function on ℝ. Let f, f′, f″ : ℝ → ℝ and M : ℝ satisfy M ≥ 0. Assume f′ is the derivative of f everywhere and f″ is the derivative of f′ everywhere. For x, y : ℝ, assume that every w in the interval between x and y satisfies |f″(w) − f″(x)| ≤ M. Then, with `abs_sub_taylor_two_le_modulus`, the Taylor remainder obeys
--
--   $$|f(y)-f(x)-f'(x)(y-x)-\tfrac12 f''(x)(y-x)^2|\le M|y-x|^2.$$
--
--   This is the one-dimensional form of the oscillation-controlled Taylor estimate and can be reused when only a bound on the second derivative’s oscillation along the relevant segment is available.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L52-L94 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_sub_taylor_two_le_modulus`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.abs_sub_taylor_two_le_modulus_408915f {f f' f'' : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {x y : ℝ} (hM : ∀ w ∈ Set.uIcc x y, |f'' w - f'' x| ≤ M) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ M * |y - x| ^ 2 := by sorry
