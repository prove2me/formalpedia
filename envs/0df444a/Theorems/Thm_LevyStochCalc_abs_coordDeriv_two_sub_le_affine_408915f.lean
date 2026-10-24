-- Prove2me | Theorems.Thm_LevyStochCalc_abs_coordDeriv_two_sub_le_affine_408915f
-- name    : LevyStochCalc.abs_coordDeriv_two_sub_le_affine_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:49:38.256979+00:00
-- url     : https://prove2.me/theorems/2349db31-fc26-4971-90a7-e1671d6f6e71
-- title:
--   Affine Oscillation Bound for Coordinate Second Derivatives
-- statement:
--   Let n : ℕ, let f″ assign a continuous bilinear map on Fin n → ℝ to each point, and let A, K : ℝ. Assume that for all z, w : Fin n → ℝ, ‖f″(z) − f″(w)‖ ≤ A + K‖z − w‖. Then for every coordinate pair p, q : Fin n and points x, y : Fin n → ℝ, the coordinate second derivative `coordDeriv₂ f″ p q` satisfies
--
--   $$|\operatorname{coordDeriv}_2(f'',p,q,x)-\operatorname{coordDeriv}_2(f'',p,q,y)|\le A+K\|x-y\|.$$
--
--   This technical lemma transfers an operator-norm oscillation estimate to individual coordinate entries.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CoordDerivative.lean#L204-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CoordDerivative`, declaration `LevyStochCalc.abs_coordDeriv₂_sub_le_affine`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}

theorem LevyStochCalc.abs_coordDeriv_two_sub_le_affine_408915f {A K : ℝ} (h : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (p q : Fin n) (x y : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y| ≤ A + K * ‖x - y‖ := by sorry
