-- Prove2me | Theorems.Thm_LevyStochCalc_abs_riemann_weighted_sub_integral_le
-- name    : LevyStochCalc.abs_riemann_weighted_sub_integral_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T23:41:31.86772+00:00
-- url     : https://prove2.me/theorems/5f68ec21-0479-4523-af71-c958fb09ab7e
-- title:
--   abs riemann weighted sub integral le
-- statement:
--   The source theorem `LevyStochCalc.abs_riemann_weighted_sub_integral_le` is extracted from `LevyStochCalc.Brownian.RiemannSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Riemann sums of a continuous weight against a bounded density

Freezing a continuous weight at the left endpoint of each cell of a partition changes the
integral of the weight against a bounded density by at most the weight's modulus of continuity
at the mesh, times the density bound, times the length of the interval.

## Main statements

* `LevyStochCalc.abs_riemann_weighted_sub_integral_le` — the Riemann-sum error bound.
-/

namespace LevyStochCalc

open MeasureTheory

theorem _root_.LevyStochCalc.abs_riemann_weighted_sub_integral_le
    {T ε δ M Kg : ℝ} (hε0 : 0 ≤ ε)
    {g h : ℝ → ℝ} (hgc : Continuous g) (hh : Measurable h)
    (hhM : ∀ s, |h s| ≤ M) (hgb : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s| ≤ Kg)
    (hgmod : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T, |x - y| ≤ δ → |g x - g y| ≤ ε)
    {m : ℕ} (t : ℕ → ℝ) (ht0 : t 0 = 0) (htm : t m = T)
    (htmono : ∀ i, i < m → t i ≤ t (i + 1)) (htmesh : ∀ i, i < m → t (i + 1) - t i ≤ δ)
    (htIcc : ∀ i, i ≤ m → t i ∈ Set.Icc (0 : ℝ) T) :
    |(∑ i ∈ Finset.range m, g (t i) * ∫ s in t i..t (i + 1), h s)
        - ∫ s in (0 : ℝ)..T, g s * h s| ≤ ε * M * T := by sorry
