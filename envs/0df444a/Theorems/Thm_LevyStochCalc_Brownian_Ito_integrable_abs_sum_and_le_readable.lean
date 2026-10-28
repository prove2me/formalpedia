-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_sum_and_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integrable_abs_sum_and_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:15.233964+00:00
-- url     : https://prove2.me/theorems/17bd37cc-5804-4e07-8559-5fe19077a354
-- title:
--   Integrability and Moment Bound for a Finite Sum
-- statement:
--   This is the finite-sum version of the absolute-moment estimate.
--
--   Let $\iota$ be a finite type, let $f_i:\Omega\to\mathbb R$ be measurable for each $i\in\iota$, and assume $|f_i|$ is integrable for every $i$. Then $\left|\sum_i f_i\right|$ is integrable and
--   $$
--   \int\left|\sum_{i\in\iota}f_i(\omega)\right|\,dP
--   \le
--   \sum_{i\in\iota}\int|f_i(\omega)|\,dP.
--   $$
--
--   This estimate is used to control finite collections of drift and stochastic-integral increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_abs_sum_and_le {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
--       (hfi : ∀ i, Integrable (fun ω => |f i ω|) P) :
--       Integrable (fun ω => |∑ i, f i ω|) P
--         ∧ ∫ ω, |∑ i, f i ω| ∂P ≤ ∑ i, ∫ ω, |f i ω| ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Next: [`integrable_sq_sum_and_le`](https://prove2.me/theorems/d4b79fef-61af-4942-9baf-cd68b6846eef).
--
--   [Source excerpt, lines 82–85](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L82-L85) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L80-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integrable_abs_sum_and_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {ι : Type*} [Fintype ι]

theorem LevyStochCalc.Brownian.Ito.integrable_abs_sum_and_le_readable {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => |f i ω|) P) :
    Integrable (fun ω => |∑ i, f i ω|) P
      ∧ ∫ ω, |∑ i, f i ω| ∂P ≤ ∑ i, ∫ ω, |f i ω| ∂P := by sorry
