-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_progressivelyMeasurable_mul_indIoc_readable
-- name    : LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:16.582815+00:00
-- url     : https://prove2.me/theorems/030165f7-acc3-4866-b777-afeba0e9b4de
-- title:
--   Progressive Measurability of a Weighted Window Indicator
-- statement:
--   This proves progressive measurability for a weighted time window.
--
--   Let $\mathcal F$ be a filtration, let $0\le a<b$, and let $V:\Omega\to\mathbb R$ satisfy:
--
--   1. $V$ is bounded;
--   2. $V$ is measurable;
--   3. $V$ is strongly measurable with respect to $\mathcal F_a$.
--
--   Then the process $(\omega,s)\mapsto V(\omega)\mathbf 1_{(a,b]}(s)$ is progressively measurable with respect to $\mathcal F$:
--   $$
--   \operatorname{ProgressivelyMeasurable}_{\mathcal F}\bigl((\omega,s)\mapsto V(\omega)\mathbf 1_{(a,b]}(s)\bigr).
--   $$
--
--   The lemma supplies the measurability condition needed to use a past weight as an Itô-integral integrand.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem progressivelyMeasurable_mul_indIoc (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
--       (ha : 0 ≤ a) (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M)
--       (hVm : Measurable V) (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
--       Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoPullOut`](https://prove2.me/theorems/ec224d62-6516-4a47-919c-197424d19554).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoIncrement`](https://prove2.me/theorems/0dacfd17-a335-4bce-a734-7c09a89723d3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stepIocMul_eval`](https://prove2.me/theorems/78e7de7a-b770-4a24-b582-8eedc3ca2e86), [`stepIocMul₀_eval`](https://prove2.me/theorems/56a8ce59-b36c-4fd6-8596-a506da0ad724).
--
--   Previous: [`stepIocMul₀_eval`](https://prove2.me/theorems/56a8ce59-b36c-4fd6-8596-a506da0ad724) · Next: [`mul_stochasticIntegralBrownian_indIoc`](https://prove2.me/theorems/13bdf081-9a6f-4dc1-a40f-ce4f657ba4ff).
--
--   [Source excerpt, lines 149–152](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean#L149-L152) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoPullOut.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoPullOut`, declaration `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean, lines 147-165). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc_readable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M)
    (hVm : Measurable V) (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s := by sorry
