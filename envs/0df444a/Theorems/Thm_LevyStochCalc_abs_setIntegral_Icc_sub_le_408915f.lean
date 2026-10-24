-- Prove2me | Theorems.Thm_LevyStochCalc_abs_setIntegral_Icc_sub_le_408915f
-- name    : LevyStochCalc.abs_setIntegral_Icc_sub_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:55:09.998488+00:00
-- url     : https://prove2.me/theorems/4d3b733d-5d3a-4a00-a308-705d2ee82d04
-- title:
--   Lipschitz Bound for Window Integrals
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be measurable, let $B\ge0$, and assume $|f(s)|\le B$ for every $s\in\mathbb R$. For all $t,t'\in\mathbb R$, the Lebesgue integrals over the intervals $[0,t']$ and $[0,t]$ satisfy
--
--   $$
--   \left|\int_{[0,t']}f(s)\,ds-\int_{[0,t]}f(s)\,ds\right|
--   \le B|t'-t|.
--   $$
--
--   The convention for negative endpoints is inherited from the set integrals over $[0,t]$. This is the deterministic Lipschitz estimate for drift increments.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/DriftIncrement.lean#L92-L123 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.DriftIncrement`, declaration `LevyStochCalc.abs_setIntegral_Icc_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory

theorem LevyStochCalc.abs_setIntegral_Icc_sub_le_408915f {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) (t t' : ℝ) :
    |(∫ s in Set.Icc (0 : ℝ) t', f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume|
      ≤ B * |t' - t| := by sorry
