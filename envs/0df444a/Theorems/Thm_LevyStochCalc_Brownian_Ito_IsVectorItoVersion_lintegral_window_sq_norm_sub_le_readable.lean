-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_window_sq_norm_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_sq_norm_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:09.412979+00:00
-- url     : https://prove2.me/theorems/5ba0ca81-961e-4cc6-88d2-8048c9dcf930
-- title:
--   Squared-Norm Window Bound for a Vector Itô-Process Version
-- statement:
--   This is an $L^2$ window estimate for a version of a vector Itô process.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $W$ and $\mathcal F$ satisfy the coordinate Brownian-filtration assumptions, and let $H_{mk}$ satisfy measurability, progressive measurability, finite squared extended integrals on positive intervals, and $|H_{mk}|\le C$ with $C\ge0$. Let $X_0$, the measurable drifts $b_m$, and a process $X$ be such that `IsVectorItoVersion` holds. Assume $B\ge0$, each drift satisfies $|b_m(\omega,s)|\le B$, and let $u,v\in\mathbb R$ satisfy $0\le u\le v$.
--
--   The joint extended integral over time and probability obeys
--   $$
--   \int_\Omega\int_{(u,v]}\operatorname{ofReal}\!\left(\|X_s(\omega)-X_u(\omega)\|^2\right)\,ds\,dP(\omega)
--   \le
--   \operatorname{ofReal}\!\left((v-u)n\left(2(B(v-u))^2+2d^2C^2(v-u)\right)\right).
--   $$
--
--   This is the window-integrated form of the vector increment estimate and is suitable for Riemann-sum arguments.
--
--   **Formalization Note** The integrals are `ENNReal` lower integrals, time is restricted to $(u,v]$, and the real expression on the right is embedded with `ENNReal.ofReal`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsVectorItoVersion.lintegral_window_sq_norm_sub_le
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
--       (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
--       (huv : u ≤ v) :
--       ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal (‖X s ω - X u ω‖ ^ 2) ∂volume ∂P
--         ≤ ENNReal.ofReal ((v - u) * ((n : ℝ)
--           * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u))))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcessWindow`](https://prove2.me/theorems/f50cced8-08df-49bf-bf67-426674e3401c).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`integral_sq_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/4ad59ff0-71f2-424a-9d06-361263c34b7c).
--
--   Previous: [`IsVectorItoVersion.lintegral_window_norm_sub_le`](https://prove2.me/theorems/f3184ccd-0e0a-4340-b558-ebc13c8392fd).
--
--   [Source excerpt, lines 92–99](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcessWindow.lean#L92-L99) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcessWindow.lean#L89-L131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcessWindow`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_sq_norm_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_sq_norm_sub_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal (‖X s ω - X u ω‖ ^ 2) ∂volume ∂P
      ≤ ENNReal.ofReal ((v - u) * ((n : ℝ)
        * (2 * (B * (v - u)) ^ 2 + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (v - u)))))) := by sorry
