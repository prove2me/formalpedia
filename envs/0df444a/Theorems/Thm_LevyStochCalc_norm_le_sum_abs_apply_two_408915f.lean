-- Prove2me | Theorems.Thm_LevyStochCalc_norm_le_sum_abs_apply_two_408915f
-- name    : LevyStochCalc.norm_le_sum_abs_apply_two_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:39:41.179545+00:00
-- url     : https://prove2.me/theorems/987ebc6c-43f3-4169-981a-690cc202a51a
-- title:
--   Bilinear Operator Norm Bound by Coordinates
-- statement:
--   This bounds a continuous bilinear form by its coordinate values.
--
--   For $n\in\mathbb N$ and a continuous linear map
--   $$
--   A:(\operatorname{Fin}(n)\to\mathbb R)\to
--   \bigl((\operatorname{Fin}(n)\to\mathbb R)\to\mathbb R\bigr),
--   $$
--   one has
--   $$
--   \|A\|\le
--   \sum_{p\in\operatorname{Fin}(n)}\sum_{q\in\operatorname{Fin}(n)}
--   \left|A(e_p)(e_q)\right|,
--   $$
--   where $e_p$ and $e_q$ are standard basis vectors.
--
--   This provides a coordinate bound for second derivatives and bilinear terms.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CoordDerivative.lean#L161-L202 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CoordDerivative`, declaration `LevyStochCalc.norm_le_sum_abs_apply₂`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.norm_le_sum_abs_apply_two_408915f (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by sorry
