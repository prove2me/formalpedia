-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_sum_pow_three_readable
-- name    : LevyStochCalc.Brownian.Ito.integrable_abs_sum_pow_three_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:07.094362+00:00
-- url     : https://prove2.me/theorems/48f45feb-9f6f-43a8-836d-11f12b473c4e
-- title:
--   Integrability of the Cubed Absolute Value of a Finite Sum
-- statement:
--   This is a finite-sum integrability lemma.
--
--   Let $\iota$ be a finite index type, let $f_i:\Omega\to\mathbb R$ be measurable for every $i\in\iota$, and assume that each $|f_i|^3$ is integrable with respect to a measure $P$. Then
--   $$
--   \omega\longmapsto\left|\sum_{i\in\iota}f_i(\omega)\right|^3
--   $$
--   is integrable with respect to $P$.
--
--   The result is independent of any probability assumption and is used to assemble third-moment estimates from finitely many coordinates or summands.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_abs_sum_pow_three {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
--       (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P) :
--       Integrable (fun ω => |∑ i, f i ω| ^ 3) P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Previous: [`integrable_sq_sum_and_le`](https://prove2.me/theorems/d4b79fef-61af-4942-9baf-cd68b6846eef) · Next: [`integrable_sq_add_and_le`](https://prove2.me/theorems/84c68f33-8dc4-400b-b0e0-ff74d29b1e54).
--
--   [Source excerpt, lines 128–130](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L128-L130) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L127-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integrable_abs_sum_pow_three`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.integrable_abs_sum_pow_three_readable {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P) :
    Integrable (fun ω => |∑ i, f i ω| ^ 3) P := by sorry
