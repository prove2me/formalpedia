-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_add_and_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integrable_abs_add_and_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:49.952098+00:00
-- url     : https://prove2.me/theorems/ee1f9d4b-e8aa-494d-8fe1-af42c7a5d32e
-- title:
--   Integrability and Moment Bound for Two Summands
-- statement:
--   This is an integrability and first-moment estimate for a sum.
--
--   Let $A,B:\Omega\to\mathbb R$ be measurable. Assume $|A|$ and $|B|$ are integrable with respect to a measure $P$. If real numbers $a,b$ satisfy
--   $$
--   \int |A|\,dP\le a,
--   \qquad
--   \int |B|\,dP\le b,
--   $$
--   then $|A+B|$ is integrable and
--   $$
--   \int |A+B|\,dP\le a+b.
--   $$
--
--   This is a reusable two-term estimate for moment bounds of process increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_abs_add_and_le {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
--       (hA : Integrable (fun ω => |A ω|) P) (hB : Integrable (fun ω => |B ω|) P)
--       {a b : ℝ} (hAle : ∫ ω, |A ω| ∂P ≤ a) (hBle : ∫ ω, |B ω| ∂P ≤ b) :
--       Integrable (fun ω => |A ω + B ω|) P ∧ ∫ ω, |A ω + B ω| ∂P ≤ a + b
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Previous: [`integrable_sq_add_and_le`](https://prove2.me/theorems/84c68f33-8dc4-400b-b0e0-ff74d29b1e54) · Next: [`integral_sq_vectorItoMartingale_sub_le`](https://prove2.me/theorems/d36fc9ed-f7c1-4780-bf4d-334940405111).
--
--   [Source excerpt, lines 171–174](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L171-L174) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L169-L186 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integrable_abs_add_and_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.integrable_abs_add_and_le_readable {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => |A ω|) P) (hB : Integrable (fun ω => |B ω|) P)
    {a b : ℝ} (hAle : ∫ ω, |A ω| ∂P ≤ a) (hBle : ∫ ω, |B ω| ∂P ≤ b) :
    Integrable (fun ω => |A ω + B ω|) P ∧ ∫ ω, |A ω + B ω| ∂P ≤ a + b := by sorry
