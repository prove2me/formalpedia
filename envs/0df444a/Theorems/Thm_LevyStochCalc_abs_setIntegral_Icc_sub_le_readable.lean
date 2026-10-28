-- Prove2me | Theorems.Thm_LevyStochCalc_abs_setIntegral_Icc_sub_le_readable
-- name    : LevyStochCalc.abs_setIntegral_Icc_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:41.719896+00:00
-- url     : https://prove2.me/theorems/a024dc62-1949-4b29-9d3e-69c1cee958e2
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
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_setIntegral_Icc_sub_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ s, |f s| ≤ B) (t t' : ℝ) :
--       |(∫ s in Set.Icc (0 : ℝ) t', f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume|
--         ≤ B * |t' - t|
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/DriftIncrement`](https://prove2.me/theorems/46f140f5-271c-46b4-a62d-8c251e00fc2b).
--
--   Supporting theorems: [`abs_setIntegral_Ioc_le`](https://prove2.me/theorems/7eab41d0-09a0-484b-9388-f6640a71836d).
--
--   Previous: [`abs_setIntegral_Ioc_le`](https://prove2.me/theorems/7eab41d0-09a0-484b-9388-f6640a71836d).
--
--   [Source excerpt, lines 93–96](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/DriftIncrement.lean#L93-L96) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/DriftIncrement.lean#L92-L123 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.DriftIncrement`, declaration `LevyStochCalc.abs_setIntegral_Icc_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory

theorem LevyStochCalc.abs_setIntegral_Icc_sub_le_readable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) (t t' : ℝ) :
    |(∫ s in Set.Icc (0 : ℝ) t', f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume|
      ≤ B * |t' - t| := by sorry
