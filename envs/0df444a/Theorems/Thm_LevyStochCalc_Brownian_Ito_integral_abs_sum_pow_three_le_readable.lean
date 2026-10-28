-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_sum_pow_three_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_sum_pow_three_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:21.562855+00:00
-- url     : https://prove2.me/theorems/8e2176da-9942-4d76-ae35-887c676c9109
-- title:
--   Third Moment Bound for a Finite Sum
-- statement:
--   This is a third absolute-moment bound for a finite family of functions.
--
--   Let $\iota$ be a finite index type, let each $f_i:\Omega\to\mathbb R$ be measurable with $|f_i|^3$ integrable, and let $c_i\in\mathbb R$ satisfy
--   $$
--   \int_\Omega|f_i|^3\,dP\le c_i
--   $$
--   for every $i$. Then
--   $$
--   \int_\Omega\left|\sum_{i\in\iota}f_i\right|^3dP
--   \le |\iota|^2\sum_{i\in\iota}c_i.
--   $$
--
--   No probability-measure assumption is required. The lemma is used to control finite sums of scalar Itô-integral increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_sum_pow_three_le {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ}
--       (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P)
--       {c : ι → ℝ} (hc : ∀ i, ∫ ω, |f i ω| ^ 3 ∂P ≤ c i) :
--       ∫ ω, |∑ i, f i ω| ^ 3 ∂P ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, c i
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoThirdMoment`](https://prove2.me/theorems/a91256d3-896e-401f-8609-adb538add313).
--
--   Supporting theorems: [`integrable_abs_sum_pow_three`](https://prove2.me/theorems/48f45feb-9f6f-43a8-836d-11f12b473c4e).
--
--   Next: [`integral_norm_pi_pow_three_le`](https://prove2.me/theorems/5d6166a6-3ea2-4998-af8d-3304ea548177).
--
--   [Source excerpt, lines 44–47](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoThirdMoment.lean#L44-L47) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoThirdMoment.lean#L41-L65 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoThirdMoment`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_sum_pow_three_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoThirdMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.integral_abs_sum_pow_three_le_readable {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P)
    {c : ι → ℝ} (hc : ∀ i, ∫ ω, |f i ω| ^ 3 ∂P ≤ c i) :
    ∫ ω, |∑ i, f i ω| ^ 3 ∂P ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, c i := by sorry
