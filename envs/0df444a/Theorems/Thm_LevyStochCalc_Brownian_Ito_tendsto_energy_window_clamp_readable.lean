-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_window_clamp_readable
-- name    : LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:04.518853+00:00
-- url     : https://prove2.me/theorems/cdd4a95d-5776-480a-ae2b-6a1001a8347e
-- title:
--   Energy Convergence of the Clamped Coefficient Mesh
-- statement:
--   Let $H_{pk}$ and $b_p$ be measurable coefficient families whose squared energies on $[0,T]$ are finite in the `ENNReal` sense. Then the combined clamping error `clampMesh P H b T` tends to zero:
--
--   $$
--   \operatorname{clampMesh}(P,H,b,T)\longrightarrow0
--   $$
--
--   as the clamping level tends to infinity. The mesh combines the drift error weighted by $T$ and the diffusion errors summed over $p$ and $k$, with the dimension factor and all integrals exactly as encoded by `clampMesh`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_energy_window_clamp {H : Fin n → Fin d → Ω → ℝ → ℝ}
--       (hm : ∀ p k, Measurable (Function.uncurry (H p k))) {b : Fin n → Ω → ℝ → ℝ}
--       (hbm : ∀ p, Measurable (Function.uncurry (b p))) {T : ℝ}
--       (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
--       (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
--       Filter.Tendsto (clampMesh P H b T) Filter.atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Supporting theorems: [`tendsto_energy_clampAt_sub`](https://prove2.me/theorems/554d2154-b037-4ba4-9d29-93ade89b3950).
--
--   Next: [`lintegral_sq_norm_clampProcess_sub_le`](https://prove2.me/theorems/3cedae93-25d4-48aa-8734-4c7f786afa37).
--
--   [Source excerpt, lines 99–106](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L99-L106) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L97-L146 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`, declaration `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

theorem LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp_readable {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k))) {b : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ p, Measurable (Function.uncurry (b p))) {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (clampMesh P H b T) Filter.atTop (𝓝 0) := by sorry
