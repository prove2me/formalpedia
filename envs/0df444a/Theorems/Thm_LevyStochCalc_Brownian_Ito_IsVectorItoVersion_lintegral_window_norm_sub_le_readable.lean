-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_window_norm_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:49.070979+00:00
-- url     : https://prove2.me/theorems/f3184ccd-0e0a-4340-b558-ebc13c8392fd
-- title:
--   ENNReal Window Bound for Vector-Process Increments
-- statement:
--   This is the $L^1$ window estimate for a version of a vector Itô process.
--
--   Let $P$ be a probability measure and let $X$ be a version of the vector Itô process driven by a $d$-dimensional Brownian motion, with $n$ state coordinates. Assume the diffusion integrands are measurable, progressively measurable, square-integrable on every positive interval, and bounded by $C\ge0$; assume the drift coordinates are measurable and bounded in absolute value by $B\ge0$. For $0\le u\le v$, the joint $\mathrm{ENNReal}$ integral over the time window $(u,v]$ satisfies
--   $$
--   \int^\!*_{\Omega}\int^\!*_{(u,v]} \operatorname{ofReal}\!\left(\|X_s-X_u\|\right)\,ds\,dP
--   \le
--   \operatorname{ofReal}\!\left((v-u)n\left(B(v-u)+dC\sqrt{v-u}\right)\right).
--   $$
--
--   Here `IsVectorItoVersion` supplies the version properties required by the estimate. The result is suited to time-window integrations in Riemann-sum arguments.
--
--   **Formalization Note** The displayed integrals are $\mathrm{ENNReal}$ lower integrals, and `ENNReal.ofReal` is applied to the real-valued norm and to the final real bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsVectorItoVersion.lintegral_window_norm_sub_le
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
--       (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
--       (huv : u ≤ v) :
--       ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal ‖X s ω - X u ω‖ ∂volume ∂P
--         ≤ ENNReal.ofReal ((v - u)
--           * ((n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u)))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcessWindow`](https://prove2.me/theorems/f50cced8-08df-49bf-bf67-426674e3401c).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`integral_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/8034fbf3-4cec-4cc1-8421-d12baf9f25de).
--
--   Next: [`IsVectorItoVersion.lintegral_window_sq_norm_sub_le`](https://prove2.me/theorems/5ba0ca81-961e-4cc6-88d2-8048c9dcf930).
--
--   [Source excerpt, lines 49–56](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcessWindow.lean#L49-L56) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcessWindow.lean#L47-L87 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcessWindow`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal ‖X s ω - X u ω‖ ∂volume ∂P
      ≤ ENNReal.ofReal ((v - u)
        * ((n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u))))) := by sorry
