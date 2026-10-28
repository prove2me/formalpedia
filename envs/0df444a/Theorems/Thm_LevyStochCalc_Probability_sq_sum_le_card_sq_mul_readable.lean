-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_sq_sum_le_card_sq_mul_readable
-- name    : LevyStochCalc.Probability.sq_sum_le_card_sq_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:58.251399+00:00
-- url     : https://prove2.me/theorems/7c556d30-1476-4749-9b82-7ef598da576d
-- title:
--   Squared Finite-Sum Bound in $[0,\infty]$
-- statement:
--   This is an elementary finite-sum inequality for nonnegative extended-real values.
--
--   For a finite set $s$ and a function $f:s\to[0,\infty]$, write $|s|$ for the cardinality of $s$. Then
--
--   $$\left(\sum_{i\in s}f(i)\right)^2\le |s|^2\sum_{i\in s}f(i)^2.$$
--
--   Here all quantities are `ENNReal` values, and the sums are finite. This bound is useful when replacing a squared coordinate sum by a sum of coordinatewise squares.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sq_sum_le_card_sq_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
--       (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Previous: [`lintegral_sq_dyadicRunMax_le`](https://prove2.me/theorems/c1b80434-c26c-49be-a883-841d52382ee6).
--
--   [Source excerpt, lines 370–371](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/DoobContinuous.lean#L370-L371) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L369-L384 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.sq_sum_le_card_sq_mul`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem LevyStochCalc.Probability.sq_sum_le_card_sq_mul_readable {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := by sorry
