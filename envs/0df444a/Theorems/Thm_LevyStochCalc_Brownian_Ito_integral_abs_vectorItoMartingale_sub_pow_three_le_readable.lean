-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_vectorItoMartingale_sub_pow_three_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_vectorItoMartingale_sub_pow_three_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:20.155695+00:00
-- url     : https://prove2.me/theorems/e79302a4-4518-490f-9961-50ba76dc4c8d
-- title:
--   Third Moment Bound for a Vector Itô Martingale Increment
-- statement:
--   This is a third absolute-moment estimate for one coordinate of a vector Itô martingale.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $W$ be a $d$-dimensional Brownian motion with coordinate Brownian filtrations, and let $H_{mk}$ satisfy the stated measurability, progressive measurability, finite squared extended-integral, and bound hypotheses with $C\ge0$ and $|H_{mk}|\le C$. Fix $p\in\operatorname{Fin}(n)$ and let $0\le u<v$. Then
--   $$
--   \int_\Omega|M_p(v)-M_p(u)|^3dP
--   \le d^2\,d\,\frac{C^2+(6+\texttt{gaussianFourthMoment})C^4}{2}
--   \,(v-u)\sqrt{v-u},
--   $$
--   where $M_p$ is the $p$th coordinate of `vectorItoMartingale`.
--
--   This combines the scalar third-moment estimates over the $d$ Brownian coordinates and is reused in the coordinatewise vector Itô-process estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_vectorItoMartingale_sub_pow_three_le (p : Fin n) {u v : ℝ} (hu : 0 ≤ u)
--       (huv : u < v) :
--       ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
--           - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω| ^ 3 ∂P
--         ≤ (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
--           * ((v - u) * Real.sqrt (v - u))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoThirdMoment`](https://prove2.me/theorems/a91256d3-896e-401f-8609-adb538add313).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Supporting theorems: [`integral_abs_sub_pow_three_le`](https://prove2.me/theorems/a7606041-e2f6-444b-9bd8-b9c435c0037c), [`integral_abs_sum_pow_three_le`](https://prove2.me/theorems/8e2176da-9942-4d76-ae35-887c676c9109).
--
--   Previous: [`integral_norm_pi_pow_three_le`](https://prove2.me/theorems/5d6166a6-3ea2-4998-af8d-3304ea548177) · Next: [`integral_abs_vectorItoProcess_sub_pow_three_le`](https://prove2.me/theorems/9000ae3c-ebf5-4d65-99b6-1c5389e78b62).
--
--   [Source excerpt, lines 110–115](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoThirdMoment.lean#L110-L115) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoThirdMoment.lean#L108-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoThirdMoment`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_vectorItoMartingale_sub_pow_three_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoThirdMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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

theorem LevyStochCalc.Brownian.Ito.integral_abs_vectorItoMartingale_sub_pow_three_le_readable (p : Fin n) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) :
    ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω| ^ 3 ∂P
      ≤ (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * ((v - u) * Real.sqrt (v - u)))) := by sorry
