-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sq_enorm_finsetSum_le_readable
-- name    : LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:34.990094+00:00
-- url     : https://prove2.me/theorems/cf9da524-3235-4f23-9dbe-288975948e0e
-- title:
--   Squared Extended Norm of a Finite Sum
-- statement:
--   For m : ℕ and a real-valued family x : Fin m → ℝ, the squared extended norm of its finite sum is bounded in `ENNReal` by m times the sum of the squared extended norms:
--
--   $$\left(\left\|\sum_{k<m}x_k\right\|_+\!:\!\mathbb{R}_{\ge0\infty}\right)^2\le m\sum_{k<m}\left(\|x_k\|_+\!:\!\mathbb{R}_{\ge0\infty}\right)^2.$$
--
--   The lemma `sq_enorm_finsetSum_le_readable` is a finite-dimensional quadratic estimate in the extended nonnegative reals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sq_enorm_finsetSum_le {m : ℕ} (x : Fin m → ℝ) :
--       (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 ≤ (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoTruncate`](https://prove2.me/theorems/7275d4a0-b19e-41be-9f18-49283c27276a).
--
--   Previous: [`tendsto_energy_clampAt_sub`](https://prove2.me/theorems/554d2154-b037-4ba4-9d29-93ade89b3950).
--
--   [Source excerpt, lines 178–179](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoTruncate.lean#L178-L179) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoTruncate.lean#L176-L195 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoTruncate`, declaration `LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTruncate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le_readable {m : ℕ} (x : Fin m → ℝ) :
    (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 ≤ (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by sorry
