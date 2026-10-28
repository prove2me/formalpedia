-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_clampAt_sub_readable
-- name    : LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:30.369856+00:00
-- url     : https://prove2.me/theorems/554d2154-b037-4ba4-9d29-93ade89b3950
-- title:
--   Energy Convergence of Scalar Clamping
-- statement:
--   Let $(\Omega,P)$ be a probability space and let $G:\Omega\times\mathbb R\to\mathbb R$ be measurable. For a window $[0,T]$, assume
--
--   $$
--   \int_\Omega\int_{[0,T]}\|G(\omega,s)\|^2\,ds\,dP<\infty.
--   $$
--
--   Then the energy of the clamped difference tends to zero:
--
--   $$
--   \int_\Omega\int_{[0,T]}
--   \|\operatorname{clampAt}(j,G(\omega,s))-G(\omega,s)\|^2\,ds\,dP
--   \longrightarrow0
--   $$
--
--   as $j\to\infty$. In Lean, the finiteness hypothesis is stated as an `ENNReal` integral being unequal to $\top$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_energy_clampAt_sub {G : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry G))
--       {T : ℝ} (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
--       Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoTruncate`](https://prove2.me/theorems/7275d4a0-b19e-41be-9f18-49283c27276a).
--
--   Next: [`sq_enorm_finsetSum_le`](https://prove2.me/theorems/cf9da524-3235-4f23-9dbe-288975948e0e).
--
--   [Source excerpt, lines 105–109](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoTruncate.lean#L105-L109) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoTruncate.lean#L104-L154 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoTruncate`, declaration `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTruncate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub_readable {G : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry G))
    {T : ℝ} (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by sorry
