-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_integral_sq_norm_vectorItoIncrement_le_readable
-- name    : LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:20.631155+00:00
-- url     : https://prove2.me/theorems/f8183882-c470-441e-b8d8-7efc9444036e
-- title:
--   Summed Squared Norm Bound Along a Uniform Grid
-- statement:
--   This is a uniform-grid estimate for squared vector Itô-process increments.
--
--   Let $(\Omega,\mathcal F,P)$, the $d$-dimensional Brownian motion, coordinate Brownian filtrations, and integrands $H_{mk}$ satisfy the stated measurability, progressive measurability, finite squared extended-integral, and boundedness assumptions with $C\ge0$. Let the measurable drifts satisfy $B\ge0$ and $|b_m|\le B$. For $T>0$, $m\ne0$, and $t_i=\operatorname{unifGrid}(T,m,i)$,
--   $$
--   \sum_{i<m}\int_\Omega\|X_{t_{i+1}}-X_{t_i}\|^2dP
--   \le n\left(2B^2T\frac{T}{m}+2d^2C^2T\right).
--   $$
--
--   This estimate shows that the sum of the second moments over the uniform partition remains bounded and is used in Taylor-remainder arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_integral_sq_norm_vectorItoIncrement_le (X₀ : Ω → Fin n → ℝ)
--       (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
--       {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
--       {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
--       ∑ i ∈ Finset.range m, ∫ ω,
--           ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
--             - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2 ∂P
--         ≤ (n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T)))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoTaylor`](https://prove2.me/theorems/e2f63476-dcbb-4f48-b908-f9b176dad140).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Supporting theorems: [`integral_sq_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/4ad59ff0-71f2-424a-9d06-361263c34b7c).
--
--   Previous: [`measurable_taylorRemainderNormed`](https://prove2.me/theorems/82f77efa-c25f-4464-bcbe-e2c70b974c2c) · Next: [`integral_abs_vectorTaylorRemainder_le_affine`](https://prove2.me/theorems/c50f87d4-01af-4809-9de8-adef3412ad18).
--
--   [Source excerpt, lines 83–90](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoTaylor.lean#L83-L90) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoTaylor.lean#L80-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoTaylor`, declaration `LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTaylor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTaylor.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le_readable (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, ∫ ω,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2 ∂P
      ≤ (n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))) := by sorry
