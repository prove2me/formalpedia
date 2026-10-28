-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_sq_add_and_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integrable_sq_add_and_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:07.220273+00:00
-- url     : https://prove2.me/theorems/84c68f33-8dc4-400b-b0e0-ff74d29b1e54
-- title:
--   Second-Moment Bound for a Sum of Two Functions
-- statement:
--   Let $A,B:\Omega\to\mathbb R$ be measurable, with $A^2$ and $B^2$ integrable under a measure $P$. If
--
--   $$\int A^2\,dP\le a,\qquad \int B^2\,dP\le b,$$
--
--   then $(A+B)^2$ is integrable and
--
--   $$\int(A+B)^2\,dP\le2a+2b.$$
--
--   This elementary estimate is useful for combining drift and martingale contributions while retaining explicit second-moment bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_sq_add_and_le {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
--       (hA : Integrable (fun ω => (A ω) ^ 2) P) (hB : Integrable (fun ω => (B ω) ^ 2) P)
--       {a b : ℝ} (hAle : ∫ ω, (A ω) ^ 2 ∂P ≤ a) (hBle : ∫ ω, (B ω) ^ 2 ∂P ≤ b) :
--       Integrable (fun ω => (A ω + B ω) ^ 2) P
--         ∧ ∫ ω, (A ω + B ω) ^ 2 ∂P ≤ 2 * a + 2 * b
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Previous: [`integrable_abs_sum_pow_three`](https://prove2.me/theorems/48f45feb-9f6f-43a8-836d-11f12b473c4e) · Next: [`integrable_abs_add_and_le`](https://prove2.me/theorems/ee1f9d4b-e8aa-494d-8fe1-af42c7a5d32e).
--
--   [Source excerpt, lines 147–151](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L147-L151) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L145-L167 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integrable_sq_add_and_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.integrable_sq_add_and_le_readable {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => (A ω) ^ 2) P) (hB : Integrable (fun ω => (B ω) ^ 2) P)
    {a b : ℝ} (hAle : ∫ ω, (A ω) ^ 2 ∂P ≤ a) (hBle : ∫ ω, (B ω) ^ 2 ∂P ≤ b) :
    Integrable (fun ω => (A ω + B ω) ^ 2) P
      ∧ ∫ ω, (A ω + B ω) ^ 2 ∂P ≤ 2 * a + 2 * b := by sorry
