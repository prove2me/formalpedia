-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_norm_vectorItoProcess_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:06.662155+00:00
-- url     : https://prove2.me/theorems/8034fbf3-4cec-4cc1-8421-d12baf9f25de
-- title:
--   First Norm Moment of a Vector Itô-Process Increment
-- statement:
--   This is a first-moment bound for the supremum norm of a vector Itô-process increment.
--
--   Let $P$ be a probability measure, let $W$ be a $d$-dimensional Brownian motion with coordinate Brownian filtrations, and let the integrands $H_{mk}$ satisfy joint measurability, progressive measurability, finite $\mathrm{ENNReal}$ squared integrals on positive intervals, and $|H_{mk}|\le C$ with $C\ge0$. Let $X=\texttt{vectorItoProcess}(W,\mathcal F,H,X_0,b)$, where each drift coordinate is measurable, $B\ge0$, and $|b_m(\omega,s)|\le B$. For $0\le u<v$,
--   $$
--   \int \|X_v-X_u\|\,dP
--   \le n\left(B(v-u)+dC\sqrt{v-u}\right),
--   $$
--   where the norm is the norm on $\mathrm{Fin}(n)\to\mathbb R$.
--
--   The norm increment is also integrable. This estimate combines coordinatewise drift and martingale bounds for later window and Riemann-sum estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_norm_vectorItoProcess_sub_le {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
--       Integrable (fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
--           - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖) P
--         ∧ ∫ ω, ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
--             - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ∂P
--           ≤ (n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u)))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integrable_abs_add_and_le`](https://prove2.me/theorems/ee1f9d4b-e8aa-494d-8fe1-af42c7a5d32e), [`integrable_abs_drift_pow`](https://prove2.me/theorems/a6288035-95df-498a-8432-a20089aba59f), [`integral_abs_vectorItoMartingale_sub_le`](https://prove2.me/theorems/8b157a78-e3e6-4128-ac91-5b7ce7b8fb41), [`measurable_vectorItoProcess_sub`](https://prove2.me/theorems/a8a3a0c4-bf0d-4b14-81c4-23f97e4dcb97), [`abs_setIntegral_Ioc_le`](https://prove2.me/theorems/7eab41d0-09a0-484b-9388-f6640a71836d).
--
--   Previous: [`measurable_vectorItoProcess_sub`](https://prove2.me/theorems/a8a3a0c4-bf0d-4b14-81c4-23f97e4dcb97) · Next: [`integral_sq_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/4ad59ff0-71f2-424a-9d06-361263c34b7c).
--
--   [Source excerpt, lines 446–451](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L446-L451) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L444-L490 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
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
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
include hbm hC0 hCH hB0 hB

theorem LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le_readable {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖) P
      ∧ ∫ ω, ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ∂P
        ≤ (n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u))) := by sorry
