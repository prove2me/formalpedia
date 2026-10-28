-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_drift_pow_readable
-- name    : LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:22.046149+00:00
-- url     : https://prove2.me/theorems/a6288035-95df-498a-8432-a20089aba59f
-- title:
--   Integrability of Powers of a Bounded Drift Increment
-- statement:
--   This proves integrability of powers of a bounded drift integral.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space and let $b^{\mathrm{drift}}:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable. Assume that for some $B\ge0$,
--   $$
--   |b^{\mathrm{drift}}(\omega,s)|\le B
--   $$
--   for every $\omega,s$. If $u
--   ot
--   gtr v$ is not assumed; rather, assume $u\le v$. Then for every $n\in\mathbb N$,
--   $$
--   \omega\longmapsto
--   \left|\int_{(u,v]}b^{\mathrm{drift}}(\omega,s)\,ds\right|^n
--   $$
--   is integrable with respect to $P$.
--
--   This supplies the all-orders integrability of bounded drift increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_abs_drift_pow
--       (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
--       {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
--       {u v : ℝ} (huv : u ≤ v) (n : ℕ) :
--       MeasureTheory.Integrable
--         (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ n) P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoProcess`](https://prove2.me/theorems/0e852a7e-a66b-4b2e-af71-2e5817bdbfa8).
--
--   Supporting theorems: [`abs_setIntegral_Ioc_le`](https://prove2.me/theorems/7eab41d0-09a0-484b-9388-f6640a71836d).
--
--   Next: [`integral_abs_sub_stochasticIntegral_le`](https://prove2.me/theorems/b9104289-b232-47cf-94d1-9015281546b4).
--
--   [Source excerpt, lines 49–54](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoProcess.lean#L49-L54) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoProcess.lean#L48-L65 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow_readable
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) (n : ℕ) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ n) P := by sorry
