-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIocMul_zero_eval_readable
-- name    : LevyStochCalc.Brownian.Ito.stepIocMul_zero_eval_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:51.070422+00:00
-- url     : https://prove2.me/theorems/56a8ce59-b36c-4fd6-8596-a506da0ad724
-- title:
--   Evaluation of the Zero-Started Window Step Integrand
-- statement:
--   This is the zero-endpoint version of the evaluation formula for `stepIocMul₀`.
--
--   Let $(\Omega,\mathcal A)$ be a measurable space, let $0<b$, and let $V:\Omega\to\mathbb R$ be bounded and measurable. For every real time $s$ and sample point $\omega$,
--   $$
--   \operatorname{stepIocMul}_0(V)(s,\omega)
--   =V(\omega)\,\mathbf 1_{(0,b]}(s).
--   $$
--
--   The result identifies the simple predictable process used on a window beginning at time zero.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stepIocMul₀_eval {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
--       (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (s : ℝ) (ω : Ω) :
--       (stepIocMul₀ Ω hb V hVb hVm).eval s ω = V ω * indIoc Ω 0 b ω s
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoPullOut`](https://prove2.me/theorems/ec224d62-6516-4a47-919c-197424d19554).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/ItoIncrement`](https://prove2.me/theorems/0dacfd17-a335-4bce-a734-7c09a89723d3).
--
--   Previous: [`stepIocMul_eval`](https://prove2.me/theorems/78e7de7a-b770-4a24-b582-8eedc3ca2e86) · Next: [`progressivelyMeasurable_mul_indIoc`](https://prove2.me/theorems/030165f7-acc3-4866-b777-afeba0e9b4de).
--
--   [Source excerpt, lines 87–89](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean#L87-L89) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoPullOut.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoPullOut`, declaration `LevyStochCalc.Brownian.Ito.stepIocMul₀_eval`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean, lines 87-102). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.stepIocMul_zero_eval_readable {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (s : ℝ) (ω : Ω) :
    (stepIocMul₀ Ω hb V hVb hVm).eval s ω = V ω * indIoc Ω 0 b ω s := by sorry
