-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_one_le_modulus_408915f
-- name    : LevyStochCalc.abs_sub_taylor_one_le_modulus_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:49:35.63903+00:00
-- url     : https://prove2.me/theorems/246be281-fab5-4636-9d25-2c6dc5122df7
-- title:
--   First-Order Taylor Remainder from Derivative Oscillation
-- statement:
--   This is a first-order Taylor remainder estimate under an oscillation bound on the derivative.
--
--   Let $f,f':\mathbb R\to\mathbb R$ and suppose that $f$ has derivative $f'(x)$ at every $x$. For $x,y\in\mathbb R$, assume that there is $M\in\mathbb R$ such that
--   $$
--   |f'(w)-f'(x)|\le M
--   $$
--   for every $w$ in the unordered interval $\operatorname{uIcc}(x,y)$. Then
--   $$
--   |f(y)-f(x)-f'(x)(y-x)|\le M|y-x|.
--   $$
--
--   This bound controls the first-order Taylor error using only the oscillation of the derivative along the segment between the two points.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L28-L50 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_sub_taylor_one_le_modulus`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.abs_sub_taylor_one_le_modulus_408915f {f f' : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) {x y : ℝ}
    (hM : ∀ w ∈ Set.uIcc x y, |f' w - f' x| ≤ M) :
    |f y - f x - f' x * (y - x)| ≤ M * |y - x| := by sorry
