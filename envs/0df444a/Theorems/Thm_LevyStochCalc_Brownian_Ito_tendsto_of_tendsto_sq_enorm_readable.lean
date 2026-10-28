-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_of_tendsto_sq_enorm_readable
-- name    : LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:37.925202+00:00
-- url     : https://prove2.me/theorems/98542836-cccb-4492-8290-6e6d19d114a0
-- title:
--   Convergence from Squared Extended-Norm Convergence
-- statement:
--   Let E be a normed additive commutative group, let u : ℕ → E, and let w : E. If
--
--   $$\left(\|u_i-w\|_+\!:\!\mathbb{R}_{\ge0\infty}\right)^2\to0$$
--
--   along the natural numbers, then u_i → w in E. The declaration `tendsto_of_tendsto_sq_enorm_readable` converts convergence of squared extended norms into ordinary topological convergence.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_of_tendsto_sq_enorm {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {w : E}
--       (h : Filter.Tendsto (fun i => (‖u i - w‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0)) :
--       Filter.Tendsto u Filter.atTop (𝓝 w)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Previous: [`lintegral_window_sq_norm_version_clamp_sub_le`](https://prove2.me/theorems/c96d8a38-efbf-4a2e-a1e2-fc59d1d0efa6) · Next: [`exists_seq_ae_tendsto_of_tendsto_lintegral`](https://prove2.me/theorems/3562f88f-3c78-4ff5-ad93-01edc45ad90f).
--
--   [Source excerpt, lines 339–341](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L339-L341) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L338-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`, declaration `LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

theorem LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm_readable {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {w : E}
    (h : Filter.Tendsto (fun i => (‖u i - w‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto u Filter.atTop (𝓝 w) := by sorry
